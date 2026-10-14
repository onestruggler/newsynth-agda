-- Quadratic extensions A[θ] of a ring A, where θ² = s + tθ for fixed
-- s, t ∈ A. A tag type G names the generator θ, and an instance
-- Generator G A supplies s and t, so that different generators over
-- the same ring give different types. The particular extensions, such
-- as ℤ[ω][ζ₁₆], ℤ[ζ₃] and ℤ[√2][2cos(π/8)] and towers over them, are in
-- Quantum.Synthesis.Ring.XiRings, and the ring laws (for all
-- generators at once) are in
-- Quantum.Synthesis.Ring.Properties.Quadratic.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Quadratic where

open import Data.Maybe.Base using (just ; _>>=_)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String ; _++_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes ; no)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Localized using (PrimeBase)

-- The generator θ named by G satisfies θ² = gen-s + gen-t θ over A.
record Generator (G A : Set) : Set where
  field
    gen-s gen-t : A
open Generator {{...}} public

-- The conjugate adj θ of the generator is gen-adj-u + gen-adj-v θ.
record AdjointGenerator (G A : Set) : Set where
  field
    gen-adj-u gen-adj-v : A
open AdjointGenerator {{...}} public

-- The value Quad a b represents a + bθ.
record Quadratic (G A : Set) : Set where
  constructor Quad
  field
    q-a q-b : A

module _ {G A : Set} {{_ : Ring A}} where
  open LiteralsFor A

  -- The generator θ itself.
  generator : Quadratic G A
  generator = Quad 0# 1#

  instance
    SemiRingQuad : {{Generator G A}} -> SemiRing (Quadratic G A)
    SemiRingQuad ._+_ (Quad a b) (Quad c d) = Quad (a + c) (b + d)
    SemiRingQuad ._*_ (Quad a b) (Quad c d) =
      Quad (a * c + gen-s {G} * (b * d)) (a * d + b * c + gen-t {G} * (b * d))
    SemiRingQuad .0# = Quad 0# 0#
    SemiRingQuad .1# = Quad 1# 0#
    SemiRingQuad .fromℕ n = Quad (fromℕ n) 0#

    RingQuad : {{Generator G A}} -> Ring (Quadratic G A)
    RingQuad .sra = SemiRingQuad
    RingQuad .-_ (Quad a b) = Quad (- a) (- b)

    NumberQuad : {{Generator G A}} -> Number (Quadratic G A)
    NumberQuad = number-from-semiring

    NegativeQuad : {{Generator G A}} -> Negative (Quadratic G A)
    NegativeQuad = negative-from-ring

    DecEqQuad : {{DecEq A}} -> DecEq (Quadratic G A)
    DecEqQuad ._≟_ (Quad a b) (Quad c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no a≠c | _ = no λ { refl -> a≠c refl }
    ... | yes _ | no b≠d = no λ { refl -> b≠d refl }

    -- Constants of A are constants of A[θ].
    HalfRingQuad : {{HalfRing A}} -> HalfRing (Quadratic G A)
    HalfRingQuad .half = Quad half 0#
    HalfRingQuad .fromℤ/2^ a n = Quad (fromℤ/2^ a n) 0#

    RootHalfRingQuad : {{RootHalfRing A}} -> RootHalfRing (Quadratic G A)
    RootHalfRingQuad .roothalf = Quad roothalf 0#
    RootHalfRingQuad .fromD[√2] a n b m = Quad (fromD[√2] a n b m) 0#

    RootTwoRingQuad : {{RootTwoRing A}} -> RootTwoRing (Quadratic G A)
    RootTwoRingQuad .roottwo = Quad roottwo 0#
    RootTwoRingQuad .fromℤ[√2] a b = Quad (fromℤ[√2] a b) 0#

    ComplexRingQuad : {{ComplexRing A}} -> ComplexRing (Quadratic G A)
    ComplexRingQuad .i = Quad i 0#

    OmegaRingQuad : {{OmegaRing A}} -> OmegaRing (Quadratic G A)
    OmegaRingQuad .omega = Quad omega 0#

    -- adj (a + bθ) = adj a + adj b · adj θ.
    AdjointQuad : {{_ : Adjoint A}} {{_ : AdjointGenerator G A}} -> Adjoint (Quadratic G A)
    AdjointQuad .adj (Quad a b) = Quad (adj a + adj b * gen-adj-u {G}) (adj b * gen-adj-v {G})

  -- Printing in the format "Quad a b".
  module _ {{_ : Show A}} where
    showsPrec-Quad : ℕ -> Quadratic G A -> String
    showsPrec-Quad p (Quad a b) = showParen p 10 ("Quad " ++ showsPrec 11 a ++ " " ++ showsPrec 11 b)

    instance
      ShowQuad : Show (Quadratic G A)
      ShowQuad .showsPrec = showsPrec-Quad

-- The constant-coefficient embedding.
lift-Quad : {G A : Set} {{_ : Ring A}} -> A -> Quadratic G A
lift-Quad a = Quad a 0#

instance
  WholePartQuad : {G A B : Set} {{_ : WholePart A B}} -> WholePart (Quadratic G A) (Quadratic G B)
  WholePartQuad .from-whole (Quad a b) = Quad (from-whole a) (from-whole b)
  WholePartQuad .to-whole (Quad a b) = Quad (to-whole a) (to-whole b)

  ToDyadicQuad : {G A B : Set} {{_ : ToDyadic A B}} -> ToDyadic (Quadratic G A) (Quadratic G B)
  ToDyadicQuad .maybe-dyadic (Quad a b) =
    maybe-dyadic a >>= λ a' -> maybe-dyadic b >>= λ b' -> just (Quad a' b')

-- Lift a base of the coefficient ring: since {1, θ} is a basis of the
-- whole ring B[θ] over B, aδᵏ is integral iff both coordinates are.
-- (Not a generic instance, to avoid overlapping with the instances for
-- bases that are not in A, such as 1 + ζ₁₆; it is registered for the
-- bases √2, 2 and p below, and clients can register it for other tags.)
DenomExpQuad : {Base G A : Set} {{_ : DenomExp Base A}} -> DenomExp Base (Quadratic G A)
DenomExpQuad {Base} .DenomExp.denomexp (Quad a b) = max (denomexpBy Base a) (denomexpBy Base b)
DenomExpQuad {Base} .DenomExp.denomexp-factor (Quad a b) k = Quad (denomexp-factorBy Base a k) (denomexp-factorBy Base b k)

instance
  DenomExpQuadSqrtTwo : {G A : Set} {{_ : DenomExp SqrtTwoBase A}} -> DenomExp SqrtTwoBase (Quadratic G A)
  DenomExpQuadSqrtTwo = DenomExpQuad

  DenomExpQuadTwo : {G A : Set} {{_ : DenomExp TwoBase A}} -> DenomExp TwoBase (Quadratic G A)
  DenomExpQuadTwo = DenomExpQuad

  DenomExpQuadPrime : {p : ℕ} {G A : Set} {{_ : DenomExp (PrimeBase p) A}} -> DenomExp (PrimeBase p) (Quadratic G A)
  DenomExpQuadPrime = DenomExpQuad
