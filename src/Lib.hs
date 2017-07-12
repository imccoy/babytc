{-# LANGUAGE UndecidableInstances #-}
module Lib
    ( typecheck
    , lam, app, var, number, text
    ) where

import           Control.Monad (void)
import           Control.Monad.Error.Class (MonadError, throwError)
import           Control.Monad.Identity (runIdentity, Identity)
import           Control.Monad.Trans (MonadTrans, lift)
import           Control.Monad.Trans.Either (runEitherT)
import           Control.Unification
import           Control.Unification.IntVar (IntVar, evalIntBindingT, IntBindingT)
import           Control.Unification.Types
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe (fromMaybe)
import           Data.Text (Text)
import           Data.Foldable (toList)

import Debug.Trace


data Node t = Node t (Expr t)
  deriving (Functor, Foldable, Traversable, Show)

data Expr t = Lam Text (Node t)
            | App (Node t) (Node t)
            | Var Text
            | Number Integer
            | Text Text
          --  | Case (Node t) [(Text, Text, Node t)]
  deriving (Functor, Foldable, Traversable, Show)

lam argName body = Node () $ Lam argName body
app fun arg = Node () $ App fun arg
var text = Node () $ Var text
number n = Node () $ Number n
text t = Node () $ Text t

class TinyFallible v a where
  undefinedVar :: Text -> v -> a

data Error t v = UndefinedVar Text v
               | UFailure (UFailure t v)

deriving instance (Show (t (UTerm t v)), Show v) => Show (Error t v)

instance Fallible TyF v (Error TyF v) where
  occursFailure a b = UFailure $ occursFailure a b
  mismatchFailure a b = UFailure $ mismatchFailure a b

instance TinyFallible v (Error TyF v) where
  undefinedVar = UndefinedVar

data TyF f = LamTy f f
           | AppTy f f
           | NumTy
           | TextTy
  deriving (Functor, Foldable, Traversable, Show)

instance Unifiable TyF where
  zipMatch (LamTy arg1 body1) (LamTy arg2 body2) = Just $ LamTy (Right (arg1, arg2)) (Right (body1, body2))
  zipMatch (AppTy fun1 arg1) (AppTy fun2 arg2) = Just $ AppTy (Right (fun1, fun2)) (Right (arg1, arg2))
  zipMatch NumTy NumTy = Just NumTy
  zipMatch TextTy TextTy = Just TextTy
  zipMatch _ _ = Nothing

type Ty v = UTerm TyF v

lamTy :: Ty v -> Ty v -> Ty v
lamTy argTy bodyTy = UTerm $ LamTy argTy bodyTy

appTy :: Ty v -> Ty v -> Ty v
appTy funTy argTy = UTerm $ AppTy funTy argTy

numTy = UTerm NumTy

textTy = UTerm TextTy

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
          => Map Text (Ty v) -> Node v -> em m (Ty v)
constrain tyEnv (Node tyVar expr) = do ty' <- go expr
                                       unify (UVar tyVar) ty'
  where go (Lam argName lamBody) = do argTy <- UVar <$> lift freeVar
                                      bodyTy <- constrain (Map.insert argName argTy tyEnv) lamBody
                                      pure (UTerm $ LamTy argTy bodyTy)
        go (App funExp argExp) = do argTy <- constrain tyEnv argExp
                                    funBodyTy <- UVar <$> lift freeVar
                                    funExpTy <- constrain tyEnv funExp
                                    funExpTy' <- pure $ UTerm $ LamTy argTy funBodyTy
                                    unify funExpTy funExpTy'
                                    pure funBodyTy
        go (Var text)
         | Just varTy <- Map.lookup text tyEnv = pure varTy
         | otherwise                           = throwError $ undefinedVar text tyVar
        go (Number _) = pure numTy
        go (Text _) = pure textTy

initialEnv :: [(Text, Ty v)]
initialEnv = [("+", lamTy numTy $ lamTy numTy $ numTy)]


typecheck :: Node () -> Either (Error TyF IntVar) (Node (UTerm TyF IntVar))
typecheck code = runIdentity $ evalIntBindingT $ runEitherT $ do tyVarCode <- lift $ (allocateTyVars code :: (IntBindingT TyF Identity) (Node IntVar))
                                                                 constrained <- constrain (Map.fromList initialEnv) tyVarCode
                                                                 applyBindingsAll (UVar <$> toList tyVarCode)
                                                                 lift $ groundTys tyVarCode
