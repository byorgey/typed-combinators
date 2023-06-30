---
title: "Compiling to Intrinsically Typed Combinators"
---

XXX goal: compile to host language.  Link to related things.

XXX talk about `Maybe`

First, some language extensions and imports.

> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE InstanceSigs #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE LambdaCase #-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE StandaloneDeriving #-}
> {-# LANGUAGE TypeOperators #-}
>
> module TypedCombinators where
>
> import Prelude hiding (lookup)
> import Data.Text ( Text )
> import Data.Kind (Type)
> import Data.Type.Equality ( type (:~:)(Refl), TestEquality(..) )

Untyped, raw terms
------------------

Here's an algebraic data type to represent raw terms of our DSL.
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
>   deriving Show

In order to keep things simple, notice that lambdas must be annotated
with the type of the argument. XXX If chosen because it is
polymorphic.  XXX Gt chosen because it is sort-of polymorphic!  XXX
say something later about extending to situation with generating
constraints, unification.

Here are our types: integers, booleans, and functions.

> data Ty where
>   TyInt  :: Ty
>   TyBool :: Ty
>   TyFun  :: Ty -> Ty -> Ty
>   deriving Show

Type-indexed constants
----------------------

That was the end of our raw, untyped representations --- from now on,
everything is going to be type-indexed!  First of all, we'll declare
an enumeration of constants, with each constant indexed by its
corresponding host language type.  These will include both any special
language built-ins (like `if`, addition, *etc.*) as well as a set of
combinators which we'll be using as a compilation target (more on
these later).  XXX say more about CIf, CGt polymorphism

> data Const :: Type -> Type where
>   CInt :: Int -> Const Int
>   CIf :: Const (Bool -> a -> a -> a)
>   CAdd :: Const (Int -> Int -> Int)
>   CGt :: Ord a => Const (a -> a -> Bool)
>   I :: Const (a -> a)
>   K :: Const (a -> b -> a)
>   S :: Const ((a -> b -> c) -> (a -> b) -> a -> c)
>   B :: Const ((     b -> c) -> (a -> b) -> a -> c)
>   C :: Const ((a -> b -> c) ->       b  -> a -> c)
>
> deriving instance Show (Const ty)

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
read as "`t` is a term with type `ty`, possibly containing variables
whose types are described by the context `g`".  Our core language has
only variables, constants, lambdas, and application.

> data TTerm :: [Type] -> Type -> Type where
>   TVar :: Idx g t -> TTerm g t
>   TConst :: Const a -> TTerm g a
>   TLam :: TTerm (ty1 ': g) ty2 -> TTerm g (ty1 -> ty2)
>   TApp :: TTerm g (a -> b) -> TTerm g a -> TTerm g b
>
> deriving instance Show (TTerm g ty)
>
> instance Applicable (TTerm g) where
>   ($$) = TApp
>
> instance HasConst (TTerm g) where
>   embed = TConst

Now for some type-indexed types!  That is, we have a term-level
representation of our DSL's types, indexed by the corresponding host
language types. XXX singletons etc., connection between term + type
levels.  XXX Pattern-matching on `TType` values lets us learn type information.

> data TType :: Type -> Type where
>   TTyInt :: TType Int
>   TTyBool :: TType Bool
>   (:->:) :: TType a -> TType b -> TType (a -> b)
>
> deriving instance Show (TType ty)

Occasionally we will need one of these type-indexed types inside an
existential wrapper; in particular when converting from a `Ty` we
can't know which type we're going to get.  `SomeType` wraps up a
`TType` with a hidden type index, and the `someType` function converts
from `Ty` to `SomeType`.

> data SomeType :: Type where
>   SomeType :: TType ty -> SomeType
>
> someType :: Ty -> SomeType
> someType TyInt = SomeType TTyInt
> someType TyBool = SomeType TTyBool
> someType (TyFun ty1 ty2) = case (someType ty1, someType ty2) of
>   (SomeType ty1', SomeType ty2') -> SomeType (ty1' :->: ty2')

Finally, a few type-related utilities.  First, we will need to be able
to test two value-level type representations for equality and have
that reflected at the level of type indices; the `TestEquality` class
from `Data.Type.Equality` is perfect for this.  The `testEquality`
function takes two type-indexed things and returns a type equality
proof wrapped in `Maybe`.

> instance TestEquality TType where
>   testEquality :: TType a -> TType b -> Maybe (a :~: b)
>   testEquality TTyInt TTyInt = Just Refl
>   testEquality TTyBool TTyBool = Just Refl
>   testEquality (ty11 :->: ty12) (ty21 :->: ty22) =
>     case (testEquality ty11 ty21, testEquality ty12 ty22) of
>       (Just Refl, Just Refl) -> Just Refl
>       _ -> Nothing
>   testEquality _ _ = Nothing

Recall that the `CGt` constant requires an `Ord` instance; the
`checkOrd` function pattern-matches on a `TType` and witnesses the
fact that the corresponding host-language type has an `Ord` instance
(if, in fact, it does).

> checkOrd :: TType ty -> (Ord ty => a) -> Maybe a
> checkOrd TTyInt a = Just a
> checkOrd TTyBool a = Just a
> checkOrd _ _ = Nothing

Type inference and elaboration
------------------------------

Now that we have our type-indexed core language all set, it's time to
translate from untyped terms (`Term`) to type-indexed ones!  First,
let's define type contexts, *i.e.* mappings from variables to their
types.  We store contexts simply as a (fancy, type-indexed) list of
variable names paired with their types.

> data Ctx :: [Type] -> Type where
>
>   -- CNil represents an empty context.
>   CNil :: Ctx '[]
>
>   -- A cons stores a variable name and its type, and then the rest of the context.
>   (:::) :: (Text, TType ty) -> Ctx g -> Ctx (ty ': g)

When looking up a variable name in the context, we can't know in
advance what index we will get and what type it will have.  But since
that information is reflected at the type level, we will have to wrap
it in an existential.  `SomeIdx g` represents an existentially wrapped
index into the context `g`.  However, we also package up a `TType`
with the type of the variable---pattern-matching on this `TType` value
will allow us to recover the type information.

> data SomeIdx :: [Type] -> Type where
>   SomeIdx :: TType ty -> Idx g ty -> SomeIdx g
>
> mapSomeIdx :: (forall ty. Idx g1 ty -> Idx g2 ty) -> SomeIdx g1 -> SomeIdx g2
> mapSomeIdx f (SomeIdx ty i) = SomeIdx ty (f i)

Now we can define the `lookup` function, which takes a variable name
and a context and tries to return a corresponding de Bruijn index into
the context.

> lookup :: Text -> Ctx g -> Maybe (SomeIdx g)
> lookup _ CNil = Nothing
> lookup x ((y, ty) ::: ctx)
>   | x == y = Just (SomeIdx ty VZ)
>   | otherwise = mapSomeIdx VS <$> lookup x ctx

Just as with variable lookups, when inferring the type of a term we
can't know in advance what type it will have, so we will need to
return an existential wrapper around a type-indexed term.  `SomeTerm`
packages up a type-indexed term along with a corresponding `TType`
value.

> data SomeTerm :: [Type] -> Type where
>   SomeTerm :: TType ty -> TTerm g ty -> SomeTerm g
>
> deriving instance Show (SomeTerm g)

Now we're finally ready to define the `infer` function!  It takes a
type context and a raw term, and tries to compute a corresponding
type-indexed term.  XXX no guarantee that we return corresponding one,
but at least the Haskell type system guarantees that we can't return a
type-incorrect term!

> infer :: Ctx g -> Term -> Maybe (SomeTerm g)

To infer the type of a literal integer value, just return `TTyInt`
with a literal integer constant.

> infer _ (Lit i) = return $ SomeTerm TTyInt (embed (CInt i))

To infer the type of a variable, look it up in the context and wrap
the result in `TVar`.  Notice how we are allowed to pattern-match on
`SomeIdx` (revealing the existentially quantified type inside) since
we immediately wrap it back up inside `SomeTerm`.

> infer ctx (Var x) = (\(SomeIdx ty i) -> SomeTerm ty (TVar i)) <$> lookup x ctx

To infer the type of a lambda, we convert the argument type annotation
to a type-indexed type, infer the type of the body under an extended
context, and then return a lambda with an appropriate function type.

> infer ctx (Lam x ty1 t) = do
>   case someType ty1 of
>     SomeType ty1' -> do
>       SomeTerm ty2 t' <- infer ((x,ty1') ::: ctx) t
>       return $ SomeTerm (ty1' :->: ty2) (TLam t')

To infer the type of an application, we infer the type of the
left-hand side, ensure it is a function type, and `check` that the
right-hand side has the correct type.  We will see the `check`
function later.

> infer ctx (App t1 t2) = do
>   SomeTerm ty1 t1' <- infer ctx t1
>   case ty1 of
>     tyArg :->: tyRes -> do
>       t2' <- check ctx t2 tyArg
>       return $ SomeTerm tyRes (TApp t1' t2')
>     _ -> Nothing

To infer the type of a `let`-expression, we infer the type of the
definition, infer the type of the body under an extended context, and
then desugar it into an application of a lambda.  That is, `let x = t1
in t2` desugars to `(\x.t2) t1`.

> infer ctx (Let x t1 t2) = do
>   SomeTerm ty1 t1' <- infer ctx t1
>   SomeTerm ty2 t2' <- infer ((x, ty1) ::: ctx) t2
>   return $ SomeTerm ty2 (TApp (TLam t2') t1')

To infer an `if`-expression, we can check that the test has type
`Bool`, infer the types of the two branches, and ensure that they are
the same.  If so, we return the `CIf` constant applied to the three
arguments.

> infer ctx (If t1 t2 t3) = do
>   t1' <- check ctx t1 TTyBool
>   SomeTerm ty2 t2' <- infer ctx t2
>   SomeTerm ty3 t3' <- infer ctx t3
>   case testEquality ty2 ty3 of
>     Nothing -> Nothing
>     Just Refl -> return $ SomeTerm ty2 (CIf .$ t1' $$ t2' $$ t3')

Addition is simple; we just check that both arguments have type `Int`.

> infer ctx (Add t1 t2) = do
>   t1' <- check ctx t1 TTyInt
>   t2' <- check ctx t2 TTyInt
>   return $ SomeTerm TTyInt (CAdd .$ t1' $$ t2')

"Greater than" is a bit interesting because we allow it to be used at
both `Int` and `Bool`.  So, just as with `if`, we must infer the types
of the arguments and check that they match.  But then we must also use
the `checkOrd` function to ensure that the argument types are an
instance of `Ord`.

> infer ctx (Gt t1 t2) = do
>   SomeTerm ty1 t1' <- infer ctx t1
>   SomeTerm ty2 t2' <- infer ctx t2
>   case testEquality ty1 ty2 of
>     Nothing -> Nothing
>     Just Refl -> (\c -> SomeTerm TTyBool (c .$ t1' $$ t2')) <$> checkOrd ty1 CGt

Finally, here's the `check` function: to check that an expression has
a given type, infer its type and make sure it's the one we expected.
Notice how this also allow us to return the type-indexed term without
using an existential wrapper, since the expected type is an input.
XXX in a real system this could be more interesting, *e.g.* nontrivial
checking cases for lambdas, pairs, etc.  Leave as an exercise.

> check :: Ctx g -> Term -> TType ty -> Maybe (TTerm g ty)
> check ctx t ty = do
>   SomeTerm ty' t' <- infer ctx t
>   case testEquality ty ty' of
>     Nothing -> Nothing
>     Just Refl -> Just t'

An aside: a typed interpreter
-----------------------------

We can now easily write an interpreter.  However, this
is pretty inefficient (it has to carry around an environment and do
linear-time lookups), and later we're going to compile our terms
directly to host language terms.  So this interpreter is just a nice
aside, for fun and testing.

With that said, given a closed term, we can interpret it directly to a
value of its corresponding host language type.  We need typed
environments and a indexing function (note that for some reason GHC
can't see that the last case of the indexing function is impossible;
if we tried implementing it in, say, Agda, we wouldn't have to write
that case).

> data Env :: [Type] -> Type where
>   ENil :: Env '[]
>   ECons :: a -> Env g -> Env (a ': g)
>
> (!) :: Env g -> Idx g ty -> ty
> (ECons x _) ! VZ = x
> (ECons _ e) ! (VS x) = e ! x
> ENil ! _ = error "GHC can't tell this is impossible"

Now the interpreter is straightforward.

> interpTTerm :: TTerm '[] ty -> ty
> interpTTerm = go ENil
>   where
>     go :: Env g -> TTerm g ty -> ty
>     go e (TVar x) = e ! x
>     go e (TLam body) = \x -> go (ECons x e) body
>     go e (TApp f x) = go e f (go e x)
>     go _ (TConst c) = interpConst c
>
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

Compiling to combinators: type-indexed bracket abstraction
----------------------------------------------------------

XXX Now, on with the main attraction!  It's well-known that certain
sets of combinators are Turing-complete: XXX for example SKI most
well-known (or SK if you're trying to be minimal).  Well-known
algorithms for compiling lambda calculus terms into combinators, XXX
*bracket abstraction*.  For example, the lambda calculus term `\x. x`
can be represented by the combinator `I`; `\x. \y. x` can be
represented by `K`; and XXX by XXX.

XXX whole point is that by making environments implicit, we make use
of the host language runtime's ability to keep track of environments.
Much more efficient.

So the idea is to compile our typed core language down to combinators.
The resulting terms will have *no* lambdas or variables---only
constants and application!  The `BTerm` type below will be the
compilation target.  Again for illustration and/or debugging we can
easily write a direct interpreter for `BTerm`---but this still isn't
the intended code path.  There will still be one more step to convert
`BTerm`s directly into host language terms.

> data BTerm :: Type -> Type where
>   BApp :: BTerm (a -> b) -> BTerm a -> BTerm b
>   BConst :: Const a -> BTerm a
>
> deriving instance Show (BTerm ty)
>
> instance Applicable BTerm where
>   ($$) = BApp
>
> instance HasConst BTerm where
>   embed = BConst
>
> interpBTerm :: BTerm ty -> ty
> interpBTerm (BApp f x) = interpBTerm f (interpBTerm x)
> interpBTerm (BConst c) = interpConst c

We will use the usual SKI combinators as well as `B` and `C`, which
are like special-case variants of `S`:

* `S x y z = x z (y z)`
* `B x y z = x   (y z)`
* `C x y z = x z (y  )`

`S` handles the application of `x` to `y` in the case where they both
need access to a shared parameter `z`; `B` and `C` are similar, but
`B` is used when only `y`, and not `x`, needs access to `z`, and `C`
is for when only `x` needs access to `z`.  Using `B` and `C` will
allow for more efficient encodings than would be possible with `S`
alone.

If you want to compile a language with recursion you can also add the
usual `Y` combinator, although we won't use it.  XXX This set of
combinators is cheekily referred to as `SICKBY`.

XXX bracket abstraction usually presented in an untyped way.  e.g. see
XXX.  But I found this [really cool paper by Oleg
Kiselyov](http://okmij.org/ftp/tagless-final/ski.pdf) where he shows
how to do bracket abstraction in a completely compositional,
type-indexed way.  I found the paper a bit hard to understand, but
fortunately it came with [working OCaml
code](http://okmij.org/ftp/tagless-final/skconv.ml)!  Translating it
to Haskell was straightforward.

> --------------------------------------------------
> -- Open terms
>
> -- These explicitly open terms are an intermediate stage in the
> -- bracket abstraction algorithm.
> data OTerm :: [Type] -> Type -> Type where
>   -- Embedded closed term.
>   E :: BTerm a -> OTerm g a
>   -- Reference to the innermost/top environment variable, i.e. Z
>   V :: OTerm (a ': g) a
>   -- Internalize the topmost env variable as a function argument
>   N :: OTerm g (a -> b) -> OTerm (a ': g) b
>   -- Ignore the topmost env variable
>   W :: OTerm g b -> OTerm (a ': g) b
>
> instance HasConst (OTerm g) where
>   embed = E . embed
>
> -- Bracket abstraction: convert the TTerm to an OTerm, then project
> -- out the embedded BTerm.  GHC can see this is total since E is the
> -- only constructor that can produce an OTerm with an empty
> -- environment.
> bracket :: TTerm '[] a -> BTerm a
> bracket t = case conv t of
>   E t' -> t'
>
> -- Type-preserving conversion from TTerm to OTerm (conv + the
> -- Applicable instance).  Taken directly from Kiselyov.
> conv :: TTerm g a -> OTerm g a
> conv (TVar VZ) = V
> conv (TVar (VS x)) = W (conv (TVar x))
> conv (TLam t) = case conv t of
>   V -> E (embed I)
>   E d -> E (K .$ d)
>   N e -> e
>   W e -> K .$ e
> conv (TApp t1 t2) = conv t1 $$ conv t2
> conv (TConst c) = embed c
>
> instance Applicable (OTerm g) where
>   W e1 $$ W e2 = W (e1 $$ e2)
>   W e $$ E d = W (e $$ E d)
>   E d $$ W e = W (E d $$ e)
>   W e $$ V = N e
>   V $$ W e = N (E (C .$. I) $$ e)
>   W e1 $$ N e2 = N (B .$ e1 $$ e2)
>   N e1 $$ W e2 = N (C .$ e1 $$ e2)
>   N e1 $$ N e2 = N (S .$ e1 $$ e2)
>   N e $$ V = N (S .$ e $. I)
>   V $$ N e = N (E (S .$. I) $$ e)
>   E d $$ N e = N (E (B .$ d) $$ e)
>   E d $$ V = N (E d)
>   V $$ E d = N (E (C .$. I $$ d))
>   N e $$ E d = N (E (C .$. C $$ d) $$ e)
>   E d1 $$ E d2 = E (d1 $$ d2)
>
>   -- GHC can tell that V $$ V is impossible (it would be ill-typed)
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
> runCTerm (CFun f) = runCTerm . f . CConst
