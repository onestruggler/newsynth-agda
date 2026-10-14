-- The rings ℤ[1/p] of fractions whose denominator is a power of a
-- fixed number p ≥ 2, such as the triadic fractions ℤ[⅓]. They play
-- the role of the dyadic fractions 𝔻 = ℤ[½] (Quantum.Synthesis.Ring)
-- for other primes, e.g. ℤ[ζ₃, 1/√-3] = ℤ[⅓][ζ₃] (see
-- Quantum.Synthesis.Ring.XiRings).
--
-- As for 𝔻, a fraction a/pⁿ is represented canonically: either n = 0
-- or p ∤ a. Hence the propositional equality on ℤ[1/ p ] is the
-- equality of numbers (for p ≥ 2; see
-- Quantum.Synthesis.Ring.Properties.Localized).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Localized where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∨_ ; T)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ ; +_ ; -[1+_])
import Data.Nat.Properties as NatP
open import Data.Rational.Base as Rat using (ℚ)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.String.Base using (_++_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Decidable.Core using (T?)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring

-- ----------------------------------------------------------------------
-- * Representation

-- suc (p ∸ 1) is p for p ≥ 1 (definitionally if p is a numeral or of
-- the form suc q), and is non-zero by construction, so that it can be
-- divided by without an instance argument.
pos : ℕ -> ℕ
pos p = suc (p Nat.∸ 1)

-- p ∣ a.
divides : ℕ -> ℤ -> Bool
divides p a = (Int.∣ a ∣ Nat.% pos p) Nat.≡ᵇ 0

CanonicalFrac : ℕ -> ℤ -> ℕ -> Bool
CanonicalFrac p a n = (n Nat.≡ᵇ 0) ∨ not (divides p a)

infix 30 ℤ[1/_]

-- The value Frac' a n _ represents a/pⁿ.
record ℤ[1/_] (p : ℕ) : Set where
  constructor Frac'
  field
    numerator : ℤ
    exponent : ℕ
    .canonical : T (CanonicalFrac p numerator exponent)

-- The triadic fractions.
Triadic : Set
Triadic = ℤ[1/ 3 ]

module _ {p : ℕ} where

  private
    ¬T⇒T-not : ∀ {b} -> ¬ T b -> T (not b)
    ¬T⇒T-not {true} ¬t = ¬t _
    ¬T⇒T-not {false} _ = _

  -- Smart constructor: frac a n = a/pⁿ. (As for dyadic, the case split
  -- is on the decision T? (divides p a), so that the definition can be
  -- reasoned about, and 0 is a shortcut.)
  frac : ℤ -> ℕ -> ℤ[1/ p ]
  frac (+ zero) _ = Frac' (+ zero) zero _
  frac a zero = Frac' a zero _
  frac a (suc n) with T? (divides p a)
  ... | yes _ = frac (a Int./ℕ pos p) n
  ... | no ¬d = Frac' a (suc n) (¬T⇒T-not ¬d)

  -- pᵏ.
  p^ : ℕ -> ℕ
  p^ k = pos p Nat.^ k

  -- Given x and k ≥ 0 such that a = xpᵏ is an integer, return a. If
  -- a is not an integer, return the floor of xpᵏ.
  integer-of-frac : ℤ[1/ p ] -> ℕ -> ℤ
  integer-of-frac (Frac' a n _) k with n Nat.≤ᵇ k
  ... | true = a Int.* + p^ (k Nat.∸ n)
  ... | false = Int._/ℕ_ a (p^ (n Nat.∸ k)) {{NatP.m^n≢0 (pos p) (n Nat.∸ k)}}

  -- Bring two fractions to a common exponent.
  align-frac : ℤ[1/ p ] -> ℤ[1/ p ] -> ℤ × ℤ × ℕ
  align-frac (Frac' a n _) (Frac' b m _) with n Nat.≤ᵇ m
  ... | true = a Int.* + p^ (m Nat.∸ n) , b , m
  ... | false = a , b Int.* + p^ (n Nat.∸ m) , n

  -- xpᵏ, without a multiplication.
  frac-shift : ℤ[1/ p ] -> ℕ -> ℤ[1/ p ]
  frac-shift (Frac' a n _) k with k Nat.≤ᵇ n
  ... | true = frac a (n Nat.∸ k)
  ... | false = Frac' (a Int.* + p^ (k Nat.∸ n)) 0 _

  instance
    SemiRingFrac : SemiRing ℤ[1/ p ]
    SemiRingFrac ._+_ x y with align-frac x y
    ... | a , b , k = frac (a Int.+ b) k
    SemiRingFrac ._*_ (Frac' a n _) (Frac' b m _) = frac (a Int.* b) (n Nat.+ m)
    SemiRingFrac .0# = Frac' 0 0 _
    SemiRingFrac .1# = Frac' 1 0 _
    SemiRingFrac .fromℕ n = Frac' (+ n) 0 _

    RingFrac : Ring ℤ[1/ p ]
    RingFrac .sra = SemiRingFrac
    RingFrac .-_ (Frac' a n _) = frac (Int.- a) n

    NumberFrac : Number ℤ[1/ p ]
    NumberFrac = number-from-semiring

    NegativeFrac : Negative ℤ[1/ p ]
    NegativeFrac = negative-from-ring

    DecEqFrac : DecEq ℤ[1/ p ]
    DecEqFrac ._≟_ (Frac' a n _) (Frac' b m _) with a ≟ b | n ≟ m
    ... | yes refl | yes refl = yes refl
    ... | no a≠b | _ = no λ { refl -> a≠b refl }
    ... | yes _ | no n≠m = no λ { refl -> n≠m refl }

    DecOrdFrac : DecOrd ℤ[1/ p ]
    DecOrdFrac = decOrd-from-bool le lt
      where
        le lt : ℤ[1/ p ] -> ℤ[1/ p ] -> Bool
        le x y with align-frac x y
        ... | a , b , _ = a ≤ᵇ b
        lt x y with align-frac x y
        ... | a , b , _ = a <ᵇ b

    AdjointFrac : Adjoint ℤ[1/ p ]
    AdjointFrac .adj x = x

    Adjoint2Frac : Adjoint2 ℤ[1/ p ]
    Adjoint2Frac .adj2 x = x

    FloorFrac : Floor ℤ[1/ p ]
    FloorFrac .floor-of x = integer-of-frac x 0
    FloorFrac .ceiling-of x = - integer-of-frac (- x) 0

    ToRationalFrac : ToRational ℤ[1/ p ]
    ToRationalFrac .toℚ (Frac' a n _) = Rat._/_ a (p^ n) {{NatP.m^n≢0 (pos p) n}}

    ShowFrac : Show ℤ[1/ p ]
    ShowFrac .showsPrec d x = showsPrec d (toℚ x)

    WholePartFrac : WholePart ℤ[1/ p ] ℤ
    WholePartFrac .from-whole a = Frac' a 0 _
    WholePartFrac .to-whole x = integer-of-frac x 0

    ToQOmegaFrac : ToQOmega ℤ[1/ p ]
    ToQOmegaFrac .toQOmega x = Omega 0 0 0 (toℚ x)

-- The inverse of p in ℤ[1/ p ] (for p ≥ 2), e.g. ⅓ : Triadic.
recip-p : {p : ℕ} -> ℤ[1/ p ]
recip-p = frac 1 1

⅓ : Triadic
⅓ = recip-p

-- The unique ring homomorphism from ℤ[1/ p ] to any ring containing
-- 1/p, given as an element.
fromFrac : {p : ℕ} {A : Set} {{_ : Ring A}} -> A -> ℤ[1/ p ] -> A
fromFrac r (Frac' a n _) = fromℤ a * r ^ n

-- ----------------------------------------------------------------------
-- * Denominator exponents with respect to p

-- The base p of ℤ[1/ p ], as a DenomExp tag. (The tag TwoBase of
-- Quantum.Synthesis.Ring plays this role for the dyadic fractions.)
data PrimeBase (p : ℕ) : Set where

ThreeBase : Set
ThreeBase = PrimeBase 3

instance
  DenomExpFrac : {p : ℕ} -> DenomExp (PrimeBase p) ℤ[1/ p ]
  DenomExpFrac .DenomExp.denomexp (Frac' _ k _) = k
  DenomExpFrac .DenomExp.denomexp-factor = frac-shift

  BaseNamePrime : {p : ℕ} -> BaseName (PrimeBase p)
  BaseNamePrime {p} .recip-name = "recip " ++ show p
  BaseNamePrime {p} .latex-name _ = show p
