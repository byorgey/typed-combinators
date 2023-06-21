> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE StandaloneDeriving #-}
> {-# LANGUAGE LambdaCase #-}
>
> module TypedCombinators where
>
> import Prelude hiding (lookup)
> import Data.Text ( Text )
> import Data.Kind (Type)
> import Data.Type.Equality ( type (:~:)(Refl), TestEquality(..) )
>
> ------------------------------------------------------------
> -- Untyped terms
>
> data Term where
>   Lit :: Int -> Term
>   Var :: Text -> Term
>   Let :: Text -> Term -> Term -> Term
>   If  :: Term -> Term -> Term -> Term
>   Add :: Term -> Term -> Term
>   Gt  :: Term -> Term -> Term
>   deriving Show
>
> ------------------------------------------------------------
> -- Type class for type-indexed application
>
> infixl 1 $$
> class Applicable t where
>   ($$) :: t (a -> b) -> t a -> t b
>
> ------------------------------------------------------------
> -- Type-indexed constants
>
> -- Includes language built-ins as well as combinators we will use
> -- later as a compilation target.
> data Const :: Type -> Type where
>   CInt :: Int -> Const Int
>   CIf :: Const (Bool -> a -> a -> a)
>   CAdd :: Const (Int -> Int -> Int)
>   CGt :: Ord a => Const (a -> a -> Bool)
>   K :: Const (a -> b -> a)
>   S :: Const ((a -> b -> c) -> (a -> b) -> a -> c)
>   I :: Const (a -> a)
>   B :: Const ((b -> c) -> (a -> b) -> a -> c)
>   C :: Const ((a -> b -> c) -> b -> a -> c)
>
> deriving instance Show (Const ty)
>
> -- Interpret constants directly into the host language.  We don't use
> -- this in our ultimate compilation but it's nice to have for
> -- debugging/comparison.
> interpConst :: Const ty -> ty
> interpConst = \case
>   (CInt i) -> i
>   CIf -> \b t e -> if b then t else e
>   CAdd -> (+)
>   CGt -> (>)
>   K -> const
>   S -> (<*>)
>   I -> id
>   B -> (.)
>   C -> flip
>
> class HasConst t where
>   injConst :: Const a -> t a
>
> infixl 1 .$
> (.$) :: (HasConst t, Applicable t) => Const (a -> b) -> t a -> t b
> c .$ t = injConst c $$ t
>
> infixl 1 $.
> ($.) :: (HasConst t, Applicable t) => t (a -> b) -> Const a -> t b
> t $. c = t $$ injConst c
>
> infixl 1 .$.
> (.$.) :: (HasConst t, Applicable t) => Const (a -> b) -> Const a -> t b
> c1 .$. c2 = injConst c1 $$ injConst c2
>
> ------------------------------------------------------------
> -- Intrinsically typed terms
>
> -- Typed de Bruijn indices.
> data Idx :: [Type] -> Type -> Type where
>   VZ :: Idx (ty ': g) ty
>   VS :: Idx g ty -> Idx (ty2 ': g) ty
>
> deriving instance Show (Idx g ty)
>
> -- Type-indexed terms.  Note this is a stripped-down core language,
> -- with only variables, lambdas, application, and constants.
> data TTerm :: [Type] -> Type -> Type where
>   TVar :: Idx g t -> TTerm g t
>   TLam :: TTerm (ty1 ': g) ty2 -> TTerm g (ty1 -> ty2)
>   TApp :: TTerm g (a -> b) -> TTerm g a -> TTerm g b
>   TConst :: Const a -> TTerm g a
>
> deriving instance Show (TTerm g ty)
>
> instance Applicable (TTerm g) where
>   ($$) = TApp
>
> instance HasConst (TTerm g) where
>   injConst = TConst
>
> ------------------------------------------------------------
> -- Type representations
>
> -- DSL types, indexed by their host language counterparts.
> data TType :: Type -> Type where
>   TyInt :: TType Int
>   TyBool :: TType Bool
>
> deriving instance Show (TType ty)
>
> -- Utilities
>
> instance TestEquality TType where
>   testEquality TyInt TyInt = Just Refl
>   testEquality TyBool TyBool = Just Refl
>   testEquality _ _ = Nothing
>
> checkOrd :: TType ty -> (Ord ty => a) -> Maybe a
> checkOrd TyInt a = Just a
> checkOrd TyBool a = Just a
>
> ------------------------------------------------------------
> -- Type checking/inference
>
> data Ctx :: [Type] -> Type where
>   CNil :: Ctx '[]
>   CCons :: Text -> TType ty -> Ctx g -> Ctx (ty ': g)
>
> data SomeIdx :: [Type] -> Type where
>   SomeIdx :: Idx g ty -> TType ty -> SomeIdx g
>
> mapSomeIdx :: (forall ty. Idx g1 ty -> Idx g2 ty) -> SomeIdx g1 -> SomeIdx g2
> mapSomeIdx f (SomeIdx i ty) = SomeIdx (f i) ty
>
> lookup :: Text -> Ctx g -> Maybe (SomeIdx g)
> lookup _ CNil = Nothing
> lookup x (CCons y ty ctx)
>   | x == y = Just (SomeIdx VZ ty)
>   | otherwise = mapSomeIdx VS <$> lookup x ctx
>
> data SomeTerm :: [Type] -> Type where
>   SomeTerm :: TType ty -> TTerm g ty -> SomeTerm g
>
> deriving instance Show (SomeTerm g)
>
> -- We simultaneously typecheck and elaborate to our typed core language.
>
> infer :: Ctx g -> Term -> Maybe (SomeTerm g)
> infer _ (Lit i) = return $ SomeTerm TyInt (TConst (CInt i))
> infer ctx (Var x) = (\(SomeIdx i ty) -> SomeTerm ty (TVar i)) <$> lookup x ctx
> infer ctx (Let x t1 t2) = do
>   SomeTerm ty1 t1' <- infer ctx t1
>   SomeTerm ty2 t2' <- infer (CCons x ty1 ctx) t2
>   return $ SomeTerm ty2 (TApp (TLam t2') t1')
> infer ctx (If t1 t2 t3) = do
>   t1' <- check ctx t1 TyBool
>   SomeTerm ty2 t2' <- infer ctx t2
>   SomeTerm ty3 t3' <- infer ctx t3
>   case testEquality ty2 ty3 of
>     Nothing -> Nothing
>     Just Refl -> return $ SomeTerm ty2 (CIf .$ t1' $$ t2' $$ t3')
> infer ctx (Add t1 t2) = do
>   t1' <- check ctx t1 TyInt
>   t2' <- check ctx t2 TyInt
>   return $ SomeTerm TyInt (CAdd .$ t1' $$ t2')
> infer ctx (Gt t1 t2) = do
>   SomeTerm ty1 t1' <- infer ctx t1
>   SomeTerm ty2 t2' <- infer ctx t2
>   case testEquality ty1 ty2 of
>     Nothing -> Nothing
>     Just Refl -> (\c -> SomeTerm TyBool (c .$ t1' $$ t2')) <$> checkOrd ty1 CGt
>
> check :: Ctx g -> Term -> TType ty -> Maybe (TTerm g ty)
> check ctx t ty = do
>   SomeTerm ty' t' <- infer ctx t
>   case testEquality ty ty' of
>     Nothing -> Nothing
>     Just Refl -> Just t'
>
> ------------------------------------------------------------
> -- Interpreting intrinsically typed terms
>
> data Env :: [Type] -> Type where
>   ENil :: Env '[]
>   (:::) :: Env g -> a -> Env (a ': g)
>
> (!) :: Env g -> Idx g ty -> ty
> (_ ::: x) ! VZ = x
> (e ::: _) ! (VS x) = e ! x
> ENil ! _ = error "Impossible!"  -- for some reason GHC can't see that this case is impossible
>
> -- An interpreter, just for comparison.
> interpTTerm :: TTerm '[] ty -> ty
> interpTTerm = go ENil
>   where
>     go :: Env g -> TTerm g ty -> ty
>     go e (TVar x) = e ! x
>     go e (TLam body) = \x -> go (e ::: x) body
>     go e (TApp f x) = go e f (go e x)
>     go _ (TConst c) = interpConst c
>
> ------------------------------------------------------------
> -- Compiling to combinators
>
> -- Explicitly type-preserving bracket abstraction, a la Oleg Kiselyov.
> -- See:
> --
> --   http://okmij.org/ftp/tagless-final/ski.pdf
> --   http://okmij.org/ftp/tagless-final/skconv.ml
>
> --------------------------------------------------
> -- Closed terms
>
> -- Closed, fully abstracted terms.  All computation is represented by
> -- combinators.  This is the target for the bracket abstraction
> -- operation.
> data BTerm :: Type -> Type where
>   BApp :: BTerm (a -> b) -> BTerm a -> BTerm b
>   BConst :: Const a -> BTerm a
>
> -- Direct interpreter for BTerm, for debugging/comparison.
> interpBTerm :: BTerm ty -> ty
> interpBTerm (BApp f x) = interpBTerm f (interpBTerm x)
> interpBTerm (BConst c) = interpConst c
>
> deriving instance Show (BTerm t)
>
> instance Applicable BTerm where
>   ($$) = BApp
>
> instance HasConst BTerm where
>   injConst = BConst
>
> --------------------------------------------------
> -- Open terms
>
> -- These explicitly open terms are an intermediate stage in the
> -- bracket abstraction algorithm.
> data OTerm :: [Type] -> Type -> Type where
>   -- Embedded closed term.
>   OC :: BTerm a -> OTerm g a
>   -- Reference to the innermost/top environment variable, i.e. Z
>   OV :: OTerm (a ': g) a
>   -- Internalize the topmost env variable as a function argument
>   ON :: OTerm g (a -> b) -> OTerm (a ': g) b
>   -- Ignore the topmost env variable
>   OW :: OTerm g b -> OTerm (a ': g) b
>
> instance HasConst (OTerm g) where
>   injConst = OC . injConst
>
> -- Bracket abstraction: convert the TTerm to an OTerm, then project
> -- out the embedded BTerm.  GHC can see this is total since OC is the
> -- only constructor that can produce an OTerm with an empty
> -- environment.
> bracket :: TTerm '[] a -> BTerm a
> bracket t = case conv t of
>   OC t' -> t'
>
> -- Type-preserving conversion from TTerm to OTerm (conv + the
> -- Applicable instance).  Taken directly from Kiselyov.
> conv :: TTerm g a -> OTerm g a
> conv (TVar VZ) = OV
> conv (TVar (VS x)) = OW (conv (TVar x))
> conv (TLam t) = case conv t of
>   OV -> OC (BConst I)
>   OC d -> OC (K .$ d)
>   ON e -> e
>   OW e -> K .$ e
> conv (TApp t1 t2) = conv t1 $$ conv t2
> conv (TConst c) = injConst c
>
> instance Applicable (OTerm g) where
>   OW e1 $$ OW e2 = OW (e1 $$ e2)
>   OW e $$ OC d = OW (e $$ OC d)
>   OC d $$ OW e = OW (OC d $$ e)
>   OW e $$ OV = ON e
>   OV $$ OW e = ON (OC (C .$. I) $$ e)
>   OW e1 $$ ON e2 = ON (B .$ e1 $$ e2)
>   ON e1 $$ OW e2 = ON (C .$ e1 $$ e2)
>   ON e1 $$ ON e2 = ON (S .$ e1 $$ e2)
>   ON e $$ OV = ON (S .$ e $. I)
>   OV $$ ON e = ON (OC (S .$. I) $$ e)
>   OC d $$ ON e = ON (OC (B .$ d) $$ e)
>   OC d $$ OV = ON (OC d)
>   OV $$ OC d = ON (OC (C .$. I $$ d))
>   ON e $$ OC d = ON (OC (C .$. C $$ d) $$ e)
>   OC d1 $$ OC d2 = OC (d1 $$ d2)
>
>   -- GHC can tell that OV $$ OV is impossible (it would be ill-typed)
>
> ------------------------------------------------------------
> -- Compiling
>
> -- Compiling to the host language. i.e. we co-opt the host language
> -- into doing evaluation for us.
>
> -- XXX more efficient than directly interpreting BTerms?  Should try
> -- benchmarking.
>
> data CTerm a where
>   CFun :: (CTerm a -> CTerm b) -> CTerm (a -> b)
>   CConst :: a -> CTerm a  -- only for non-functions!
>
> instance Applicable CTerm where
>   CFun f $$ x = f x
>     -- above only gives a non-exhaustive warning since we can't express the fact
>     -- that CConst can't contain a function
>
> compile :: BTerm a -> CTerm a
> compile (BApp b1 b2) = compile b1 $$ compile b2
> compile (BConst c) = compileConst c
>
> compileConst :: Const a -> CTerm a
> compileConst = \case
>   (CInt i) -> CConst i
>   CIf      -> CFun $ \(CConst b) -> CFun $ \t -> CFun $ \e -> if b then t else e
>   CAdd     -> binary (+)
>   CGt      -> binary (>)
>   K        -> CFun $ \x -> CFun $ \_ -> x
>   S        -> CFun $ \f -> CFun $ \g -> CFun $ \x -> f $$ x $$ (g $$ x)
>   I        -> CFun id
>   B        -> CFun $ \f -> CFun $ \g -> CFun $ \x -> f $$ (g $$ x)
>   C        -> CFun $ \f -> CFun $ \x -> CFun $ \y -> f $$ y $$ x
>
> binary :: (a -> b -> c) -> CTerm (a -> b -> c)
> binary op = CFun $ \(CConst x) -> CFun $ \(CConst y) -> CConst (op x y)
>
> runCTerm :: CTerm a -> a
> runCTerm (CConst a) = a
>   -- Above might not be sufficient if we can actually have functions in our language.
>   -- Can only use runCTerm at a non-function type.
>
