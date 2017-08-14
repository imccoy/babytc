{-# LANGUAGE UndecidableInstances #-}
module Lib
    ( ExprF(..), Expr, TyF(..)
    , lam, app, var, lett, number, text
    , lamTy, numTy, textTy
    , lamTy', numTy', textTy'
    , runTypecheck, evalTypecheck, evalGeneralisedTypecheck, typecheck
    ) where

import           Control.Monad ((<=<), void, forM)
import           Control.Monad.Error.Class (MonadError, throwError)
import           Control.Monad.Identity (runIdentity, Identity)
import           Control.Monad.Trans (MonadTrans, lift)
import           Control.Monad.Trans.Either (EitherT, runEitherT)
import           Control.Unification
import           Control.Unification.IntVar (IntVar(..), evalIntBindingT, runIntBindingT, IntBindingT, IntBindingState)
import           Control.Unification.Types
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import           Data.Set (Set)
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Functor.Fixedpoint (Fix(..), hmapM, cata, cataM)
import           Data.Foldable (toList)

import Debug.Trace

import FoldableUterm

data ExprF f = Lam Text f
            | App f f
            | Var Text
            | Let [(Text, f)] f
            | Number Integer
            | Text Text
          --  | Case (Node t) [(Text, Text, Node t)]
  deriving (Functor, Foldable, Traversable, Show, Eq)

type Expr = Fix ExprF

lam :: Text -> Expr -> Expr
lam argName body = Fix $ Lam argName body
app fun arg = Fix $ App fun arg
var text = Fix $ Var text
lett bindings expr = Fix $ Let bindings expr
number n = Fix $ Number n
text t = Fix $ Text t


class TinyFallible v a where
  undefinedVar   :: Text -> v -> a
  undefinedTyVar :: v -> a

data Error t v = UndefinedVar Text v
               | UndefinedTyVar v
               | UFailure (UFailure t v)

deriving instance (Show (t (UTerm t v)), Show v) => Show (Error t v)

instance Fallible TyF v (Error TyF v) where
  occursFailure a b = UFailure $ occursFailure a b
  mismatchFailure a b = UFailure $ mismatchFailure a b

instance TinyFallible v (Error TyF v) where
  undefinedVar = UndefinedVar
  undefinedTyVar = UndefinedTyVar

data TyF f = LamTy f f
           | NumTy
           | TextTy
  deriving (Functor, Foldable, Traversable, Show)

instance Unifiable TyF where
  zipMatch (LamTy arg1 body1) (LamTy arg2 body2) = Just $ LamTy (Right (arg1, arg2)) (Right (body1, body2))
  zipMatch NumTy NumTy = Just NumTy
  zipMatch TextTy TextTy = Just TextTy
  zipMatch _ _ = Nothing

type Ty v = UTerm TyF v

lamTy :: Ty v -> Ty v -> Ty v
lamTy argTy bodyTy = UTerm $ LamTy argTy bodyTy

numTy = UTerm NumTy

textTy = UTerm TextTy


lamTy' argTy bodyTy = Fix $ LamTy argTy bodyTy

numTy' = Fix NumTy

textTy' = Fix TextTy


data AnnExprF ann f = AnnExprF ann (ExprF f)
  deriving (Functor, Foldable, Traversable, Show, Eq)

type AnnExpr ann = Fix (AnnExprF ann)

annFromAnnExpr :: AnnExpr a -> a
annFromAnnExpr (Fix (AnnExprF ann _)) = ann


type TyVardExpr v = AnnExpr v
type TypedExpr v = AnnExpr (Ty v)

exprMap1 :: (Monad m) => (a -> m b) -> ExprF a -> m (ExprF b)
exprMap1 = mapM 

exprChildNodes :: ExprF a -> [a]
exprChildNodes = foldMap pure



data NeedsFreshening = NeedsFreshening | SoFreshAlready

withAnn e ann = AnnExprF ann e

allocateTyVars :: forall t v m. (BindingMonad t v m, t ~ TyF) => Expr -> m (TyVardExpr v)
allocateTyVars = hmapM $ \e -> withAnn e <$> freeVar

allAnns :: TyVardExpr v -> [v]
allAnns = cata $ concat . toList 

groundTys :: forall v m. (BindingMonad TyF v m) => TyVardExpr v -> m (TypedExpr v)
groundTys = hmapM $ \(AnnExprF v e) -> withAnn e <$> manyLookup (UVar v)
  where manyLookup :: UTerm TyF v -> m (UTerm TyF v)
        manyLookup (UVar v) = lookupVar v >>= \case
                                Just v' -> manyLookup v'
                                Nothing -> pure $ UVar v
        manyLookup (UTerm t) = UTerm <$> mapM manyLookup t 

constrain :: (BindingMonad t v m, Fallible t v e, TinyFallible v e, MonadTrans em, Functor (em m), MonadError e (em m), t ~ TyF, Show v)
          => Map Text (NeedsFreshening, Ty v) -> TyVardExpr v -> em m (Ty v)
constrain tyEnv (Fix (AnnExprF tyVar expr)) = do ty' <- go expr
                                                 lift $ bindVar tyVar ty'
                                                 pure ty'
  where go (Lam argName lamBody) = do argTy <- UVar <$> lift freeVar
                                      bodyTy <- constrain (Map.insert argName (SoFreshAlready, argTy) tyEnv) lamBody
                                      pure (UTerm $ LamTy argTy bodyTy)
        go (App funExp argExp) = do argTy <- constrain tyEnv argExp
                                    funBodyTy <- UVar <$> lift freeVar
                                    funExpTy <- constrain tyEnv funExp
                                    unify (UTerm $ LamTy argTy funBodyTy) funExpTy
                                    pure funBodyTy
        go (Let bindings bodyExp) = do bindingTys <- sequence . flip Map.mapWithKey (Map.fromList bindings) $ \name exp -> do
                                         stubVar <- UVar <$> lift freeVar
                                         realVar <- constrain (Map.insert name (SoFreshAlready, stubVar) tyEnv) exp
                                         (NeedsFreshening,) <$> (stubVar =:= realVar)
                                       constrain (Map.union bindingTys tyEnv) bodyExp
                                       
        go (Var text)
         | Just (NeedsFreshening, varTy) <- Map.lookup text tyEnv = freshen varTy
         | Just (SoFreshAlready, varTy)  <- Map.lookup text tyEnv = pure varTy
         | otherwise                                              = throwError $ undefinedVar text tyVar
        go (Number _) = pure numTy
        go (Text _) = pure textTy


constrain' :: forall e m em t v. (BindingMonad t v m, Fallible t v e, TinyFallible v e, MonadTrans em, Functor (em m), MonadError e (em m), t ~ TyF, Show v)
           => Map Text (NeedsFreshening, Ty v) -> TyVardExpr v -> em m (Ty v)
constrain' tyEnv tyVardExpr = cata alg tyVardExpr $ tyEnv
  where
    alg :: AnnExprF v (Map Text (NeedsFreshening, Ty v) -> em m (Ty v))
        -> (Map Text (NeedsFreshening, Ty v) -> em m (Ty v))
    alg v@(AnnExprF tyVar expr) tyEnv
       = do expr' <- case expr of
                       (Lam argName fBodyTy) -> do argTy <- UVar <$> lift freeVar
                                                   bodyTy <- fBodyTy $ Map.insert argName (SoFreshAlready, argTy) tyEnv
                                                   pure . UTerm $ LamTy argTy bodyTy
                       (App fFunExpTy fArgTy) -> do argTy <- fArgTy tyEnv
                                                    funBodyTy <- UVar <$> lift freeVar
                                                    funExpTy <- fFunExpTy tyEnv
                                                    unify (UTerm $ LamTy argTy funBodyTy) funExpTy
                                                    pure funBodyTy
                       (Let bindings fBodyTy) -> do bindingTys <- sequence . flip Map.mapWithKey (Map.fromList bindings) $ \bindingName fBindingTy -> do
                                                      stubVar <- UVar <$> lift freeVar
                                                      realVar <- fBindingTy $ Map.insert bindingName (SoFreshAlready, stubVar) tyEnv
                                                      (NeedsFreshening,) <$> (stubVar =:= realVar)
                                                    fBodyTy $ Map.union bindingTys tyEnv
 
                       (Var text)
                         | Just (NeedsFreshening, varTy) <- Map.lookup text tyEnv -> freshen varTy
                         | Just (SoFreshAlready, varTy)  <- Map.lookup text tyEnv -> pure varTy
                         | otherwise                                              -> throwError $ undefinedVar text tyVar
                       (Number _) -> pure numTy
                       (Text _) -> pure textTy
            lift $ bindVar tyVar expr'
            pure expr'


data ForallTyF f = Forall [Text] (ForallTyF f)
                 | TyVar Text
                 | HereTy (f (ForallTyF f))

instance (Show (f (ForallTyF f))) => Show (ForallTyF f)
  where showsPrec d (TyVar t) = (T.unpack t ++)
        showsPrec d (HereTy t) = showsPrec d t
        showsPrec d (Forall ns ty) = showParen (d > app_prec) $
                                        ("Forall [" ++ ) . 
                                        (List.intercalate "," (T.unpack <$> ns) ++) .
                                        ("] " ++ ) .
                                        showsPrec d ty
          where app_prec = 10


type ForallTy = ForallTyF TyF


data ForallTyd e = ForallTyd ForallTy e
  deriving (Functor, Foldable, Traversable, Show)

deriving instance (Eq ForallTy, Eq e) => Eq (ForallTyd e)

data ForallTydExprF f = ForallTydExprF (ForallTyd (ExprF f))
  deriving (Functor, Foldable, Traversable, Show)

deriving instance (Eq ForallTy, Eq e) => Eq (ForallTydExprF e)

type ForallTydExpr = Fix ForallTydExprF

para :: Functor f => (f (Fix f, a) -> a) -> Fix f -> a
para f = snd . cata (\v -> (Fix (fst <$> v), f v))

paraM :: (Traversable f, Functor f, Monad m) => (f (Fix f, a) -> m a) -> Fix f -> m a
paraM f = fmap snd . cataM (\v -> do v' <- f v
                                     pure (Fix (fst <$> v), v'))

generalise :: forall t v e m em. (BindingMonad t v m, t ~ TyF, Show v, Variable v, MonadError e (em m), MonadTrans em, TinyFallible v e) => TypedExpr v -> em m ForallTydExpr
generalise expr = withLowestForalls <$> annotatedWithTyVarIds expr >>= \(f, _) -> f Map.empty
  where withLowestForalls :: Fix (AnnExprF (Ty v, Set Int)) -> (Map Int Text -> em m ForallTydExpr, Set Int)
        withLowestForalls = cata $ \(AnnExprF (ty, tyVarIds) expr) -> (\tyEnv -> do let childTyVarSets = snd <$> toList expr
                                                                                    let childTyVarMaps = Map.fromSet (const (1 :: Int)) <$> childTyVarSets
                                                                                    let counts = Map.unionsWith (+) childTyVarMaps
                                                                                    let singleAppearances = Map.filter (== 1) counts
                                                                                    hereVars <- lift $ fmap getVarID <$> getFreeVars ty
                                                                                    let forallOnes = List.filter (`Map.member` singleAppearances) hereVars
                                                                                    let forallManies = Map.keys . Map.filter (>1) $ counts
                                                                                    let forallIds = List.filter (`Map.notMember` tyEnv) $ forallOnes ++ forallManies
                                                                                    let usedNames = Set.fromList . Map.elems $ tyEnv
                                                                                    let names = filter (`Set.notMember` usedNames) ["t" `T.append` (T.pack . show $ n) | n <- [(0::Int)..]]
                                                                                    let newNameIds = zip forallIds names
                                                                                    let newNames = Map.fromList newNameIds
                                                                                    let newTyEnv = newNames `Map.union` tyEnv
                                                                                    expr' <- traverse (\(f, _) -> f newTyEnv) expr
                                                                                    ty' <- forallTy newTyEnv ty
                                                                                    if null newNameIds
                                                                                      then pure $ Fix $ ForallTydExprF $ ForallTyd ty' expr'
                                                                                      else pure $ Fix $ ForallTydExprF $ ForallTyd (Forall (snd <$> newNameIds) ty') expr'
                                                                      ,tyVarIds)

        annotatedWithTyVarIds :: TypedExpr v -> em m (Fix (AnnExprF (Ty v, Set Int)))
        annotatedWithTyVarIds = cataM $ \(AnnExprF ty expr) -> do hereVars <- lift $ getFreeVars ty
                                                                  let hereVarIds = Set.fromList (getVarID <$> hereVars)
                                                                  let thereIds = snd . annFromAnnExpr <$> toList expr
                                                                  pure . Fix $ AnnExprF (ty, Set.unions $ hereVarIds:thereIds) expr

        forallTy :: Map Int Text -> Ty v -> em m ForallTy
        forallTy env = cataM alg . refix . buildUTermF
          where alg (UTermF t) = pure $ HereTy t
                alg (UVarF v) | Just n <- Map.lookup (getVarID v) env = pure . TyVar $ n
                              | otherwise                             = throwError (undefinedTyVar v)

initialEnv :: [(Text, Ty v)]
initialEnv = [("+", lamTy numTy $ lamTy numTy $ numTy)
             ,("inc", lamTy numTy numTy)
             ]

typecheck :: Expr -> EitherT (Error TyF IntVar) (IntBindingT TyF Identity) (TypedExpr IntVar)
typecheck code = do tyVarCode <- lift $ allocateTyVars code
                    constrained <- constrain' (Map.fromList [(k, (NeedsFreshening, v)) | (k, v) <- initialEnv]) tyVarCode
                    applyBindingsAll (UVar <$> allAnns tyVarCode)
                    lift $ groundTys tyVarCode
                    --pure (UVar <$> tyVarCode)

evalTypecheck :: Expr -> Either (Error TyF IntVar) (TypedExpr IntVar)
evalTypecheck code = runIdentity $ evalIntBindingT $ runEitherT $ typecheck code

evalGeneralisedTypecheck :: Expr -> Either (Error TyF IntVar) (ForallTydExpr)
evalGeneralisedTypecheck code = runIdentity $ evalIntBindingT $ runEitherT $ (generalise <=< typecheck) code

runTypecheck :: Expr -> (Either (Error TyF IntVar) (TypedExpr IntVar), IntBindingState TyF)
runTypecheck code = runIdentity $ runIntBindingT $ runEitherT $ typecheck code

