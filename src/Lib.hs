{-# LANGUAGE UndecidableInstances #-}
module Lib
    ( Node(..), Expr(..), TyF(..)
    , lam, app, var, lett, number, text
    , lamTy, numTy, textTy
    , lamTy', numTy', textTy'
    , runTypecheck, evalTypecheck, evalGeneralisedTypecheck, typecheck
    ) where

import           Control.Monad ((<=<), void)
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
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Functor.Fixedpoint (Fix(..))
import           Data.Foldable (toList)

import Debug.Trace

data Node t = Node t (Expr t)
  deriving (Functor, Traversable, Show, Eq)

data Expr t = Lam Text (Node t)
            | App (Node t) (Node t)
            | Var Text
            | Let [(Text, Node t)] (Node t)
            | Number Integer
            | Text Text
          --  | Case (Node t) [(Text, Text, Node t)]
  deriving (Functor, Foldable, Traversable, Show, Eq)

instance Foldable Node where
  foldMap f (Node v e) = f v `mappend` (foldMap f e)

exprMap1 :: (Functor m, Applicative m) => (Node t1 -> m (Node t2)) -> Expr t1 -> m (Expr t2)
exprMap1 f (Lam t n) = Lam t <$> f n
exprMap1 f (App n1 n2) = App <$> f n1 <*> f n2
exprMap1 f (Let tns n) = Let <$> traverse (\(t, n) -> (t,) <$> f n) tns <*> f n
exprMap1 _ (Var v) = pure $ Var v
exprMap1 _ (Number n) = pure $ Number n
exprMap1 _ (Text t) = pure $ Text t

lam argName body = Node () $ Lam argName body
app fun arg = Node () $ App fun arg
var text = Node () $ Var text
lett bindings expr = Node () $ Let bindings expr
number n = Node () $ Number n
text t = Node () $ Text t


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

data NeedsFreshening = NeedsFreshening | SoFreshAlready

allocateTyVars :: forall t v m. BindingMonad t v m => Node () -> m (Node v)
allocateTyVars = mapM $ \() -> freeVar

groundTys :: forall v m. (BindingMonad TyF v m) => Node v -> m (Node (Ty v))
groundTys = mapM $ \v -> manyLookup (UVar v)
  where manyLookup :: UTerm TyF v -> m (UTerm TyF v)
        manyLookup (UVar v) = lookupVar v >>= \case
                                Just v' -> manyLookup v'
                                Nothing -> pure $ UVar v
        manyLookup (UTerm t) = UTerm <$> mapM manyLookup t 

constrain :: (BindingMonad t v m, Fallible t v e, TinyFallible v e, MonadTrans em, Functor (em m), MonadError e (em m), t ~ TyF, Show v)
          => Map Text (NeedsFreshening, Ty v) -> Node v -> em m (Ty v)
constrain tyEnv (Node tyVar expr) = do ty' <- go expr
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
        go (Let bindings bodyExp) = do bindingTys <- traverse (\(name, exp) -> ((name,) . (NeedsFreshening,)) <$> constrain tyEnv exp) bindings
                                       constrain (Map.union (Map.fromList bindingTys) tyEnv) bodyExp
                                       
        go (Var text)
         | Just (NeedsFreshening, varTy) <- Map.lookup text tyEnv = freshen varTy
         | Just (SoFreshAlready, varTy)  <- Map.lookup text tyEnv = pure varTy
         | otherwise                                              = throwError $ undefinedVar text tyVar
        go (Number _) = pure numTy
        go (Text _) = pure textTy

data ForallTyR f = ForallF [Text] f
                 | TyVarF Text
                 | HereTyF f

deriving instance (Show f) => Show (ForallTyR f)

data ForallTyW f = ForallTyW (ForallTyR (TyF f))

deriving instance (Show f) => Show (ForallTyW f)

type ForallTy = Fix ForallTyW

commonTyVars :: (BindingMonad t v m, t ~ TyF, Variable v) => Map Int Text -> Ty v -> Ty v -> m [(Int, Text)]
commonTyVars env ty1 ty2 = do ty1FreeVars <- getFreeVars ty1
                              ty2FreeVars <- getFreeVars ty2
                              let common = List.intersect (getVarID <$> ty1FreeVars) (getVarID <$> ty2FreeVars) List.\\ (Map.keys env)
                              let usedNames = Map.elems env
                              let names = filter (`List.notElem` usedNames) . fmap (T.pack . ("t" ++) . show) $ [0..]
                              pure $ zip common names

                              

generalise :: forall t v e m em. (BindingMonad t v m, t ~ TyF, Show v, Variable v, MonadError e (em m), MonadTrans em, TinyFallible v e) => Node (Ty v) -> em m (Node ForallTy)
generalise = go Map.empty
  where go :: Map Int Text -> Node (Ty v) -> em m (Node ForallTy)
        go env (Node (UTerm (LamTy argTy resTy)) exp) = do newTyVars <- Map.fromList <$> (lift $ commonTyVars env argTy resTy)
                                                           let newEnv = Map.union newTyVars env
                                                           ty <- LamTy <$> go' newEnv argTy <*> go' newEnv resTy
                                                           exp' <- exprMap1 (go newEnv) exp
                                                           pure $ Node (Fix . ForallTyW . ForallF (Map.elems newTyVars) $ ty) exp'
        go env (Node ty exp) = Node <$> go' env ty <*> exprMap1 (go env) exp

        go' :: Map Int Text -> Ty v -> em m ForallTy
        go' env (UTerm (LamTy argTy resTy)) = do newTyVars <- Map.fromList <$> (lift $ commonTyVars env argTy resTy)
                                                 let newEnv = Map.union newTyVars env
                                                 ty <- LamTy <$> go' newEnv argTy <*> go' newEnv resTy
                                                 pure . Fix . ForallTyW . ForallF (Map.elems newTyVars) $ ty
        go' env (UTerm TextTy) = pure . Fix . ForallTyW . HereTyF $ TextTy
        go' env (UTerm NumTy) = pure . Fix . ForallTyW . HereTyF $ NumTy
        go' env (UVar v) | Just n <- Map.lookup (getVarID v) env = pure . Fix . ForallTyW . TyVarF $ n
                         | otherwise                             = throwError (undefinedTyVar v)



initialEnv :: [(Text, Ty v)]
initialEnv = [("+", lamTy numTy $ lamTy numTy $ numTy)
             ,("inc", lamTy numTy numTy)
             ]

typecheck :: Node () -> EitherT (Error TyF IntVar) (IntBindingT TyF Identity) (Node (Ty IntVar))
typecheck code = do tyVarCode <- lift $ allocateTyVars code
                    constrained <- constrain (Map.fromList [(k, (NeedsFreshening, v)) | (k, v) <- initialEnv]) tyVarCode
                    applyBindingsAll (UVar <$> toList tyVarCode)
                    lift $ groundTys tyVarCode
                    --pure (UVar <$> tyVarCode)

evalTypecheck :: Node () -> Either (Error TyF IntVar) (Node (UTerm TyF IntVar))
evalTypecheck code = runIdentity $ evalIntBindingT $ runEitherT $ typecheck code

evalGeneralisedTypecheck :: Node () -> Either (Error TyF IntVar) (Node ForallTy)
evalGeneralisedTypecheck code = runIdentity $ evalIntBindingT $ runEitherT $ (generalise <=< typecheck) code

runTypecheck :: Node () -> (Either (Error TyF IntVar) (Node (UTerm TyF IntVar)), IntBindingState TyF)
runTypecheck code = runIdentity $ runIntBindingT $ runEitherT $ typecheck code


