-- Pure cubic extensions A[θ] of a ring A, where θ³ = s for a fixed
-- s ∈ A, e.g. ℤ[ζ₉] = ℤ[ζ₃][θ] with θ³ = ζ₃ (see
-- Quantum.Synthesis.Ring.XiRings). As in
-- Quantum.Synthesis.Ring.Quadratic, a tag type G names the generator,
-- and the ring laws (for all generators at once) are in
-- Quantum.Synthesis.Ring.Properties.Cubic.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Cubic where

open import Data.Maybe.Base using (just ; _>>=_)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String ; _++_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes ; no)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Localized using (PrimeBase)

-- The generator θ named by G satisfies θ³ = cubic-s over A.
record CubicGenerator (G A : Set) : Set where
  field
    cubic-s : A
open CubicGenerator {{...}} public

-- The conjugate adj θ of the generator is u₀ + u₁θ + u₂θ².
record AdjointCubicGenerator (G A : Set) : Set where
  field
    cubic-adj-u₀ cubic-adj-u₁ cubic-adj-u₂ : A
open AdjointCubicGenerator {{...}} public

-- The value Cub a b c represents a + bθ + cθ².
record Cubic (G A : Set) : Set where
  constructor Cub
  field
    c-a c-b c-c : A

module _ {G A : Set} {{_ : Ring A}} where
  open LiteralsFor A

  -- The generator θ itself.
  cubic-generator : Cubic G A
  cubic-generator = Cub 0# 1# 0#

  instance
    -- (a + bθ + cθ²)(a' + b'θ + c'θ²), with θ³ = s and θ⁴ = sθ.
    SemiRingCub : {{CubicGenerator G A}} -> SemiRing (Cubic G A)
    SemiRingCub ._+_ (Cub a b c) (Cub a' b' c') = Cub (a + a') (b + b') (c + c')
    SemiRingCub ._*_ (Cub a b c) (Cub a' b' c') =
      Cub (a * a' + cubic-s {G} * (b * c' + c * b'))
          (a * b' + b * a' + cubic-s {G} * (c * c'))
          (a * c' + b * b' + c * a')
    SemiRingCub .0# = Cub 0# 0# 0#
    SemiRingCub .1# = Cub 1# 0# 0#
    SemiRingCub .fromℕ n = Cub (fromℕ n) 0# 0#

    RingCub : {{CubicGenerator G A}} -> Ring (Cubic G A)
    RingCub .sra = SemiRingCub
    RingCub .-_ (Cub a b c) = Cub (- a) (- b) (- c)

    NumberCub : {{CubicGenerator G A}} -> Number (Cubic G A)
    NumberCub = number-from-semiring

    NegativeCub : {{CubicGenerator G A}} -> Negative (Cubic G A)
    NegativeCub = negative-from-ring

    DecEqCub : {{DecEq A}} -> DecEq (Cubic G A)
    DecEqCub ._≟_ (Cub a b c) (Cub a' b' c') with a ≟ a' | b ≟ b' | c ≟ c'
    ... | yes refl | yes refl | yes refl = yes refl
    ... | no p | _ | _ = no λ { refl -> p refl }
    ... | yes _ | no p | _ = no λ { refl -> p refl }
    ... | yes _ | yes _ | no p = no λ { refl -> p refl }

    -- Constants of A are constants of A[θ].
    HalfRingCub : {{HalfRing A}} -> HalfRing (Cubic G A)
    HalfRingCub .half = Cub half 0# 0#
    HalfRingCub .fromℤ/2^ a n = Cub (fromℤ/2^ a n) 0# 0#

    ComplexRingCub : {{ComplexRing A}} -> ComplexRing (Cubic G A)
    ComplexRingCub .i = Cub i 0# 0#

    -- adj (a + bθ + cθ²) = adj a + adj b · u + adj c · u², where
    -- u = adj θ = u₀ + u₁θ + u₂θ².
    AdjointCub : {{_ : Adjoint A}} {{_ : CubicGenerator G A}} {{_ : AdjointCubicGenerator G A}} -> Adjoint (Cubic G A)
    AdjointCub .adj (Cub a b c) = lift (adj a) + lift (adj b) * u + lift (adj c) * u * u
      where
        lift : A -> Cubic G A
        lift x = Cub x 0# 0#
        u : Cubic G A
        u = Cub (cubic-adj-u₀ {G}) (cubic-adj-u₁ {G}) (cubic-adj-u₂ {G})

  -- Printing in the format "Cub a b c".
  module _ {{_ : Show A}} where
    showsPrec-Cub : ℕ -> Cubic G A -> String
    showsPrec-Cub p (Cub a b c) =
      showParen p 10 ("Cub " ++ showsPrec 11 a ++ " " ++ showsPrec 11 b ++ " " ++ showsPrec 11 c)

    instance
      ShowCub : Show (Cubic G A)
      ShowCub .showsPrec = showsPrec-Cub

-- The constant-coefficient embedding.
lift-Cub : {G A : Set} {{_ : Ring A}} -> A -> Cubic G A
lift-Cub a = Cub a 0# 0#

instance
  WholePartCub : {G A B : Set} {{_ : WholePart A B}} -> WholePart (Cubic G A) (Cubic G B)
  WholePartCub .from-whole (Cub a b c) = Cub (from-whole a) (from-whole b) (from-whole c)
  WholePartCub .to-whole (Cub a b c) = Cub (to-whole a) (to-whole b) (to-whole c)

  ToDyadicCub : {G A B : Set} {{_ : ToDyadic A B}} -> ToDyadic (Cubic G A) (Cubic G B)
  ToDyadicCub .maybe-dyadic (Cub a b c) =
    maybe-dyadic a >>= λ a' -> maybe-dyadic b >>= λ b' -> maybe-dyadic c >>= λ c' -> just (Cub a' b' c')

-- Lift a base of the coefficient ring (since {1, θ, θ²} is a basis of
-- the whole ring B[θ] over B); registered for the bases 2 and p.
DenomExpCub : {Base G A : Set} {{_ : DenomExp Base A}} -> DenomExp Base (Cubic G A)
DenomExpCub {Base} .DenomExp.denomexp (Cub a b c) =
  max (denomexpBy Base a) (max (denomexpBy Base b) (denomexpBy Base c))
DenomExpCub {Base} .DenomExp.denomexp-factor (Cub a b c) k =
  Cub (denomexp-factorBy Base a k) (denomexp-factorBy Base b k) (denomexp-factorBy Base c k)

instance
  DenomExpCubTwo : {G A : Set} {{_ : DenomExp TwoBase A}} -> DenomExp TwoBase (Cubic G A)
  DenomExpCubTwo = DenomExpCub

  DenomExpCubPrime : {p : ℕ} {G A : Set} {{_ : DenomExp (PrimeBase p) A}} -> DenomExp (PrimeBase p) (Cubic G A)
  DenomExpCubPrime = DenomExpCub
