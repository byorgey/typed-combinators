XXX

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE StandaloneDeriving #-}
> {-# LANGUAGE LambdaCase #-}
>
> module TypedApplicativeCombinators where
>
> import Prelude hiding (lookup)
> import Data.Text ( Text )
> import Data.Kind (Type)
> import Data.Type.Equality ( type (:~:)(Refl), TestEquality(..) )

Untyped, raw terms
------------------

Here's an algebraic data type to represent raw terms of our language.
I've put in just enough features to make it nontrivial, but there's
not much: we have integer literals, variables, lambdas, application, `let`, `if`,
addition, and comparison with `>`.  Of course, it would be easy to add
more base types and constants.

> data Term where
>   Lit :: Int -> Term
>   Var :: Text -> Term
>   Lam :: Text -> Ty -> Term -> Term
>   App :: Term -> Term -> Term
>   Let :: Text -> Term -> Term -> Term
>   If  :: Term -> Term -> Term -> Term
>   Add :: Term -> Term -> Term
>   Gt  :: Term -> Term -> Term
>   X   :: Term
>   deriving Show

> data Op where
>   OIf :: Op
>   OAdd :: Op
>   OGt :: Op

In order to keep things simple, notice that lambdas must be annotated
with the type of the argument. XXX say something later about extending
to situation with generating constraints, unification.

Here are our types: integers, booleans, and functions.

> data Ty where
>   TyInt  :: Ty
>   TyBool :: Ty
>   TyFun  :: Ty -> Ty -> Ty
>   TyW    :: Ty -> Ty
>   deriving Show

> type W a = Int -> a

Type-indexed constants
----------------------

That was the end of our raw, untyped representations --- from now on,
everything is going to be type-indexed!  First of all, we'll declare
an enumeration of constants, with each constant indexed by its
corresponding host language type.  These will include both any special
language built-ins (like `if`, addition, *etc.*) as well as a set of
combinators which we'll be using as a compilation target (more on
these later).

> data Const :: Type -> Type where
>   CInt :: Int -> Const Int
>   CIf :: TType a -> Const (Bool -> a -> a -> a)
>   CAdd :: Const (Int -> Int -> Int)
>   CGt :: Ord a => TType a -> Const (a -> a -> Bool)
>   CX  :: Const (W Int)
>   I :: Const (a -> a)
>   K :: Const (a -> b -> a)
>   S :: Const ((a -> b -> c) -> (a -> b) -> a -> c)
>   B :: Const ((     b -> c) -> (a -> b) -> a -> c)
>   C :: Const ((a -> b -> c) ->       b  -> a -> c)
>
> deriving instance Show (Const ty)

Just for fun and/or debugging, it's easy to interpret constants
directly into the host language, although we're not actually going to
use this.

> interpConst :: Const ty -> ty
> interpConst = \case
>   (CInt i) -> i
>   CIf _ -> \b t e -> if b then t else e
>   CAdd -> (+)
>   CGt _ -> (>)
>   CX  -> id
>   K -> const
>   S -> (<*>)
>   I -> id
>   B -> (.)
>   C -> flip

For convenience, we make a type class `HasConst` for type-indexed
things that can contain embedded constants (we will end up with
several of them).

> class HasConst t where
>   embed :: Const a -> t a

Also for convenience, here's a type class for type-indexed things that
support some kind of application operation. (Note that we don't
necessarily want to require `t` to support a `pure :: a -> t a`
operation, or even be a `Functor`, so using `Applicative` would not be
appropriate.)

> infixl 1 $$
> class Applicable t where
>   ($$) :: t (a -> b) -> t a -> t b

Note that, unlike Haskell's `$` operator, `$$` is *left*-associative,
so, for example, `f $$ x $$ y` should be read just like `f x y`, that
is, `f $$ x $$ y = (f $$ x) $$ y`.

Finally, we'll spend a bunch of time applying constants to things, or
applying things to constants, so here are a few convenience operators
for combining application `$$` and `embed`:

> infixl 1 .$
> (.$) :: (HasConst t, Applicable t) => Const (a -> b) -> t a -> t b
> c .$ t = embed c $$ t
>
> infixl 1 $.
> ($.) :: (HasConst t, Applicable t) => t (a -> b) -> Const a -> t b
> t $. c = t $$ embed c
>
> infixl 1 .$.
> (.$.) :: (HasConst t, Applicable t) => Const (a -> b) -> Const a -> t b
> c1 .$. c2 = embed c1 $$ embed c2


Type-indexed types and terms
----------------------------

Now let's build up our type-indexed core language.  Note we're not
just making a type-indexed version of our original term language; for
simplicity, we're going to simultaneously typecheck and elaborate down
to a simpler core language.  Of course, it would also be entirely
possible to introduce another intermediate data type for type-indexed
terms and separate the typechecking and elaboration phases.

First, a data type for type-indexed de Bruijn indices.  A value of
type `Idx g ty` is a variable with type `ty` in the context `g`
(represented as a type-level list of types).  For example, `Idx
[Int,Bool,Int] Int` would be a variable of type `Int` (and hence must
either be variable 0 or 2).

> data Idx :: [Type] -> Type -> Type where
>   VZ :: Idx (ty ': g) ty
>   VS :: Idx g ty -> Idx (ty2 ': g) ty
>
> deriving instance Show (Idx g ty)

Now we can build our type-indexed terms.  Just like variables, terms
are indexed by a typing context and a type; `t : TTerm g ty` can be
read as "in context `g`, `t` is a term with type `ty`".  Our core
language has only variables, constants, lambdas, application, and
constants.

> data TTerm :: [Type] -> Type -> Type where
>   TVar :: Idx g t -> TTerm g t
>   TConst :: Const a -> TTerm g a
>   TLam :: TTerm (ty1 ': g) ty2 -> TTerm g (ty1 -> ty2)
>   TApp :: TTerm g (a -> b) -> TTerm g a -> TTerm g b
>
> deriving instance Show (TTerm g ty)
>
> instance Applicable (TTerm g) where
>   TConst I $$ x = x
>   f $$ x = TApp f x
>
> instance HasConst (TTerm g) where
>   embed = TConst



> ------------------------------------------------------------
> -- Type representations
>
> -- DSL types, indexed by their host language counterparts.
> data TType :: Type -> Type where
>   TTyInt :: TType Int
>   TTyBool :: TType Bool
>   (:->:) :: TType a -> TType b -> TType (a -> b)
>   TTyW :: TType a -> TType (W a)
>
> infixr 0 :->:
>
> deriving instance Show (TType ty)
>
> data SomeType :: Type where
>   SomeType :: TType ty -> SomeType
>
> someType :: Ty -> SomeType
> someType TyInt = SomeType TTyInt
> someType TyBool = SomeType TTyBool
> someType (TyFun ty1 ty2) = case (someType ty1, someType ty2) of
>   (SomeType ty1', SomeType ty2') -> SomeType (ty1' :->: ty2')
> someType (TyW ty) = case someType ty of
>   SomeType ty' -> SomeType (TTyW ty')
>
> -- Utilities
>
> instance TestEquality TType where
>   testEquality TTyInt TTyInt = Just Refl
>   testEquality TTyBool TTyBool = Just Refl
>   testEquality (ty11 :->: ty12) (ty21 :->: ty22) =
>     case (testEquality ty11 ty21, testEquality ty12 ty22) of
>       (Just Refl, Just Refl) -> Just Refl
>       _ -> Nothing
>   testEquality (TTyW ty1) (TTyW ty2) = case testEquality ty1 ty2 of
>     Just Refl -> Just Refl
>     Nothing -> Nothing
>   testEquality _ _ = Nothing
>
> checkOrd :: TType ty -> (Ord ty => a) -> Maybe a
> checkOrd TTyInt a = Just a
> checkOrd TTyBool a = Just a
> checkOrd _ _ = Nothing
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
> getBaseType :: SomeTerm g -> SomeType
> getBaseType (SomeTerm (TTyW ty) _) = SomeType ty
> getBaseType (SomeTerm ty _) = SomeType ty
>
> -- Application is where we deal with lifting + promotion.
> apply :: SomeTerm g -> SomeTerm g -> Maybe (SomeTerm g)
> apply (SomeTerm (ty11 :->: ty12) t1) (SomeTerm ty2 t2)
>   | Just Refl <- testEquality ty11 ty2 = return $ SomeTerm ty12 (t1 $$ t2)
> apply (SomeTerm (TTyW ty11 :->: ty12) t1) (SomeTerm ty2 t2)
>   | Just Refl <- testEquality ty11 ty2 = return $ SomeTerm ty12 (t1 $$ (K .$ t2))
> apply (SomeTerm (ty11 :->: ty12) t1) (SomeTerm (TTyW ty2) t2)
>   | Just Refl <- testEquality ty11 ty2 = return $ SomeTerm (TTyW ty12) (B .$ t1 $$ t2)
> apply (SomeTerm (TTyW (ty11 :->: ty12)) t1) (SomeTerm ty2 t2)
>   | Just Refl <- testEquality ty11 ty2 = return $ SomeTerm (TTyW ty12) (S .$ t1 $$ (K .$ t2))
> apply (SomeTerm (TTyW (ty11 :->: ty12)) t1) (SomeTerm (TTyW ty2) t2)
>   | Just Refl <- testEquality ty11 ty2 = return $ SomeTerm (TTyW ty12) (S .$ t1 $$ t2)
> apply _ _ = Nothing
>
> applyTo :: SomeTerm g -> SomeTerm g -> Maybe (SomeTerm g)
> applyTo = flip apply
>
> inferOp :: [SomeType] -> Op -> Maybe (SomeTerm g)
> inferOp _ OAdd = return $ SomeTerm (TTyInt :->: TTyInt :->: TTyInt) (embed CAdd)
> inferOp [SomeType tyA] OGt = SomeTerm (tyA :->: tyA :->: TTyBool) <$> checkOrd tyA (embed (CGt tyA))
> inferOp [SomeType tyA] OIf = return $ SomeTerm (TTyBool :->: tyA :->: tyA :->: tyA) (embed (CIf tyA))
> inferOp _ _ = error "bad call to inferOp"

> applyOp :: Ctx g -> ([SomeTerm g] -> [SomeType]) -> Op -> [Term] -> Maybe (SomeTerm g)
> applyOp ctx typeArgs op ts = do
>   tts <- mapM (infer ctx) ts
>   foldl (\r -> (r >>=) . applyTo) (inferOp (typeArgs tts) op) tts

> infer :: Ctx g -> Term -> Maybe (SomeTerm g)
> infer _ (Lit i) = return $ SomeTerm TTyInt (TConst (CInt i))
> infer ctx (Var x) = (\(SomeIdx i ty) -> SomeTerm ty (TVar i)) <$> lookup x ctx
> infer ctx (Lam x ty1 t) = do
>   case someType ty1 of
>     SomeType ty1' -> do
>       SomeTerm ty2 t' <- infer (CCons x ty1' ctx) t
>       return $ SomeTerm (ty1' :->: ty2) (TLam t')
> infer ctx (App t1 t2) = do
>   t1' <- infer ctx t1
>   t2' <- infer ctx t2
>   apply t1' t2'
> infer ctx (Let x t1 t2) = do
>   st1@(SomeTerm ty1 _) <- infer ctx t1
>   SomeTerm ty2 tt2 <- infer (CCons x ty1 ctx) t2
>   apply (SomeTerm (ty1 :->: ty2) (TLam tt2)) st1
> infer ctx (If t1 t2 t3) = applyOp ctx ((:[]) . getBaseType . (!!1)) OIf [t1,t2,t3]
> infer ctx (Add t1 t2) = applyOp ctx (const []) OAdd [t1,t2]
> infer ctx (Gt t1 t2) = applyOp ctx ((:[]) . getBaseType . head) OGt [t1,t2]
> infer _ X = return $ SomeTerm (TTyW TTyInt) (TConst CX)
>
> check :: Ctx g -> Term -> TType ty -> Maybe (TTerm g ty)
> check ctx t ty = do
>   t1 <- infer ctx t
>   SomeTerm ty' t' <- apply (SomeTerm (ty :->: ty) (embed I)) t1
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

  We have the
usual SKI combinators as well as `B` and `C`, which are like special-case
variants of `S`:

* `S x y z = x z (y z)`
* `B x y z = x   (y z)`
* `C x y z = x z (y  )`

`S` handles the application of `x` to `y` in the case where they both
need access to a shared parameter `z`; `B` and `C` are similar, but
`B` is used when only `y`, and not `x`, needs access to `z`, and `C`
is for when only `x` needs access to `z`.  Using `B` and `C` will
allow for more efficient encodings than would be possible with `S`
alone.


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
>   embed = BConst
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
>   embed = OC . embed
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
> conv (TConst c) = embed c
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
>     -- above only gives a non-exhaustive warning since we can't express the constraint
>     -- that CConst isn't allowed contain a function
>   _ $$ _ = error "impossible! bad call to CTerm.$$"
>
> compile :: BTerm a -> CTerm a
> compile (BApp b1 b2) = compile b1 $$ compile b2
> compile (BConst c) = compileConst c
>
> compileConst :: Const a -> CTerm a
> compileConst = \case
>   (CInt i) -> CConst i
>   CIf _    -> CFun $ \(CConst b) -> CFun $ \t -> CFun $ \e -> if b then t else e
>   CAdd     -> binary (+)
>   CGt _    -> binary (>)
>   CX       -> CFun id
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
> runCTerm (CFun f) = runCTerm . f . CConst

------------------------------------------------------------
-- Example stuff

> ex :: Term
> ex = If (Gt X (Lit 3)) (Add (Lit 2) X) (Lit 5)

> pretty :: TTerm g ty -> String
> pretty (TVar _) = undefined
> pretty (TConst c) = show c
> pretty (TApp t1 t2) = "(" ++ pretty t1 ++ " " ++ pretty t2 ++ ")"
