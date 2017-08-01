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
import           Data.Functor.Fixedpoint (Fix(..), hmapM, cata)
import           Data.Foldable (toList)

import Debug.Trace

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


data TyVard v e = TyVard v e
  deriving (Functor, Foldable, Traversable, Show, Eq)

data TyVardExprF v f = TyVardExprF (TyVard v (ExprF f))
  deriving (Functor, Foldable, Traversable, Show, Eq)

type TyVardExpr v = Fix (TyVardExprF v)


data Typed v e = Typed (Ty v) e
  deriving (Functor, Foldable, Traversable, Show)

deriving instance (Eq (Ty v), Eq e) => Eq (Typed v e)

data TypedExprF v f = TypedExprF (Typed v (ExprF f))
  deriving (Functor, Foldable, Traversable, Show)

deriving instance (Eq (Ty v), Eq e) => Eq (TypedExprF v e)

type TypedExpr v = Fix (TypedExprF v)

exprMap1 :: (Monad m) => (a -> m b) -> ExprF a -> m (ExprF b)
exprMap1 = mapM 

exprChildNodes :: ExprF a -> [a]
exprChildNodes = foldMap pure



data NeedsFreshening = NeedsFreshening | SoFreshAlready

withTyVar e v = TyVard v e
withType e v = Typed v e

allocateTyVars :: forall t v m. (BindingMonad t v m, t ~ TyF) => Expr -> m (TyVardExpr v)
allocateTyVars = hmapM $ \e -> TyVardExprF . withTyVar e <$> freeVar

allTyVars :: TyVardExpr v -> [v]
allTyVars = cata $ concat . toList 

groundTys :: forall v m. (BindingMonad TyF v m) => TyVardExpr v -> m (TypedExpr v)
groundTys = hmapM $ \(TyVardExprF (TyVard v e)) -> TypedExprF . withType e <$> manyLookup (UVar v)
  where manyLookup :: UTerm TyF v -> m (UTerm TyF v)
        manyLookup (UVar v) = lookupVar v >>= \case
                                Just v' -> manyLookup v'
                                Nothing -> pure $ UVar v
        manyLookup (UTerm t) = UTerm <$> mapM manyLookup t 

constrain :: (BindingMonad t v m, Fallible t v e, TinyFallible v e, MonadTrans em, Functor (em m), MonadError e (em m), t ~ TyF, Show v)
          => Map Text (NeedsFreshening, Ty v) -> TyVardExpr v -> em m (Ty v)
constrain tyEnv (Fix (TyVardExprF (TyVard tyVar expr))) = do ty' <- go expr
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


--deriving instance (Show (f (ForallTyF f))) => Show (ForallTyF f)

type ForallTy = ForallTyF TyF


data ForallTyd e = ForallTyd ForallTy e
  deriving (Functor, Foldable, Traversable, Show)

deriving instance (Eq ForallTy, Eq e) => Eq (ForallTyd e)

data ForallTydExprF f = ForallTydExprF (ForallTyd (ExprF f))
  deriving (Functor, Foldable, Traversable, Show)

deriving instance (Eq ForallTy, Eq e) => Eq (ForallTydExprF e)

type ForallTydExpr = Fix ForallTydExprF


generalise :: forall t v e m em. (BindingMonad t v m, t ~ TyF, Show v, Variable v, MonadError e (em m), MonadTrans em, TinyFallible v e) => TypedExpr v -> em m ForallTydExpr
generalise = goTop Map.empty
  where goTop :: Map Int Text -> TypedExpr v -> em m ForallTydExpr
        goTop env node@(Fix (TypedExprF (Typed ty expr))) = do vars <- collectNonLetFreeVarIDs node
                                                               let newVarIDs = Set.filter (`Map.notMember` env) vars
                                                               let usedNames = Map.elems env
                                                               let candidateNames = filter (`List.notElem` usedNames) . fmap (T.pack . ("t" ++) . show) $ [0..]
                                                               let newEnvElems = zip (Set.toList newVarIDs) candidateNames
                                                               let newEnv = Map.union (Map.fromList newEnvElems) env
                                                               (Fix (ForallTydExprF (ForallTyd ty' expr'))) <- go newEnv node
                                                               pure $ Fix $ ForallTydExprF $ ForallTyd (Forall (snd <$> newEnvElems) ty') expr'

        collectNonLetFreeVarIDs :: TypedExpr v -> em m (Set Int)
        collectNonLetFreeVarIDs (Fix (TypedExprF (Typed ty expr))) = do fvs <- Set.fromList <$> (fmap getVarID <$> lift (getFreeVars ty))
                                                                        Set.union fvs <$> case expr of
                                                                          Let _ body -> collectNonLetFreeVarIDs body
                                                                          _ -> Set.unions <$> mapM collectNonLetFreeVarIDs (exprChildNodes expr)

        go :: Map Int Text -> TypedExpr v -> em m (ForallTydExpr)
        go env (Fix (TypedExprF (Typed ty (Let bindings body)))) = do ty' <- go' env ty
                                                                      bindings' <- forM bindings $ \(name, exp) -> (name,) <$> goTop env exp
                                                                      body' <- go env body
                                                                      pure . Fix . ForallTydExprF $ ForallTyd ty' (Let bindings' body')
        go env (Fix (TypedExprF (Typed ty exp))) = do ty' <- go' env ty
                                                      (Fix . ForallTydExprF . ForallTyd ty') <$> exprMap1 (go env) exp

        go' :: Map Int Text -> Ty v -> em m ForallTy
        go' env (UTerm (LamTy argTy resTy)) = HereTy <$> (LamTy <$> go' env argTy <*> go' env resTy)
        go' env (UTerm TextTy) = pure . HereTy $ TextTy
        go' env (UTerm NumTy) = pure . HereTy $ NumTy
        go' env (UVar v) | Just n <- Map.lookup (getVarID v) env = pure . TyVar $ n
                         | otherwise                             = throwError (undefinedTyVar v)

initialEnv :: [(Text, Ty v)]
initialEnv = [("+", lamTy numTy $ lamTy numTy $ numTy)
             ,("inc", lamTy numTy numTy)
             ]

typecheck :: Expr -> EitherT (Error TyF IntVar) (IntBindingT TyF Identity) (TypedExpr IntVar)
typecheck code = do tyVarCode <- lift $ allocateTyVars code
                    constrained <- constrain (Map.fromList [(k, (NeedsFreshening, v)) | (k, v) <- initialEnv]) tyVarCode
                    applyBindingsAll (UVar <$> allTyVars tyVarCode)
                    lift $ groundTys tyVarCode
                    --pure (UVar <$> tyVarCode)

evalTypecheck :: Expr -> Either (Error TyF IntVar) (TypedExpr IntVar)
evalTypecheck code = runIdentity $ evalIntBindingT $ runEitherT $ typecheck code

evalGeneralisedTypecheck :: Expr -> Either (Error TyF IntVar) (ForallTydExpr)
evalGeneralisedTypecheck code = runIdentity $ evalIntBindingT $ runEitherT $ (generalise <=< typecheck) code

runTypecheck :: Expr -> (Either (Error TyF IntVar) (TypedExpr IntVar), IntBindingState TyF)
runTypecheck code = runIdentity $ runIntBindingT $ runEitherT $ typecheck code

