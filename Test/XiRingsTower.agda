-- Tests for the ξ-rings of Quantum.Synthesis.Ring.XiRings from Tables
-- 7.1 and 7.2 of Kliuchnikov–Schönnenbeck (arXiv:2405.19302): the
-- towers ℤ[ζ₃₂], ℤ[ζ₉], ℤ[2cos(π/16)], ℤ[2cos(π/32)], and ℤ[√2] with
-- the denominator 2 + √2, checked by evaluation.

{-# OPTIONS --without-K --safe #-}

module Test.XiRingsTower where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
import Data.Nat.Base as Nat
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.List.Base using (List ; [] ; _∷_ ; map ; concatMap ; foldr ; _++_)
open import Data.Product.Base using (_,_)
open import Function.Base using (_∋_)
open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Localized
open import Quantum.Synthesis.Ring.Quadratic
open import Quantum.Synthesis.Ring.Cubic
open import Quantum.Synthesis.Ring.XiRings
open import Quantum.Synthesis.Matrix hiding (Plus ; Times)

private
  -- Independent oracle (as in Test.Ring): multiply by the actual base,
  -- test integrality by a WholePart round trip, and reject every
  -- smaller exponent.
  check-denominator : {A B : Set} (Base : Set)
    {{_ : Ring A}} {{_ : DecEq A}} {{_ : WholePart A B}} {{_ : DenomExp Base A}} -> A -> A -> Bool
  check-denominator {A} {B} Base base x =
    integral (x * base ^ k) ∧ no-smaller k x ∧
    (denomexp-factorBy Base x (suc k) == x * base ^ (suc k))
    where
      k = denomexpBy Base x
      integral : A -> Bool
      integral y = from-whole {A} {B} (to-whole y) == y
      no-smaller : ℕ -> A -> Bool
      no-smaller zero y = true
      no-smaller (suc n) y = not (integral y) ∧ no-smaller n (y * base)

  all : {A : Set} -> (A -> Bool) -> List A -> Bool
  all f = foldr (λ a b -> f a ∧ b) true

  ceil-div : ℕ -> ℕ -> ℕ
  ceil-div n zero = zero
  ceil-div n d@(suc _) = (n Nat.+ d Nat.∸ 1) Nat./ d

-- ⅓ in ℤ[ζ₃, ⅓] and ℤ[ζ₉, ⅓].
⅓′ : TZeta3
⅓′ = lift-Quad ⅓

⅓″ : TZeta9
⅓″ = lift-Cub ⅓′
-- ----------------------------------------------------------------------
-- * The rings of Tables 7.1 and 7.2

-- ζ₃₂² = ζ₁₆, ζ₉³ = ζ₃, and θₖ₊₁² = 2 + θₖ for θₖ = 2cos(π/2ᵏ).
_ : (ZZeta32 ∋ ζ₃₂ ^ 2) ≡ lift-Quad ζ₁₆
_ = refl
_ : (ZZeta32 ∋ ζ₃₂ ^ 16) ≡ -1
_ = refl
_ : (ZZeta32 ∋ adj ζ₃₂ * ζ₃₂) ≡ 1
_ = refl
_ : (ZZeta9 ∋ ζ₉ ^ 3) ≡ lift-Cub ζ₃
_ = refl
_ : (ZZeta9 ∋ ζ₉ ^ 6 + ζ₉ ^ 3 + 1) ≡ 0
_ = refl
_ : (ZZeta9 ∋ adj ζ₉ * ζ₉) ≡ 1
_ = refl
_ : (ZCos16 ∋ twocos16 ^ 2) ≡ 2 + lift-Quad twocos8
_ = refl
_ : (ZCos32 ∋ twocos32 ^ 2) ≡ 2 + lift-Quad twocos16
_ = refl
_ : (ZCos32 ∋ adj twocos32) ≡ twocos32
_ = refl

-- (2 + √2)² = 2(3 + 2√2), with the unit 3 + 2√2 = (1 + √2)².
_ : denomexpBy TwoPlusRootTwoBase (DRootTwo ∋ ½) ≡ 2
_ = refl
_ : denomexp-decomposeBy {DRootTwo} {ZRootTwo} TwoPlusRootTwoBase ½ ≡ (RootTwo 3 2 , 2)
_ = refl
_ : denomexpBy OnePlusZeta32Base (DZeta32 ∋ ½) ≡ 16
_ = refl
_ : denomexpBy OneMinusZeta9Base (TZeta9 ∋ ⅓″) ≡ 6
_ = refl
_ : denomexpBy TwoPlusTwoCos16Base (DCos16 ∋ ½) ≡ 8
_ = refl
_ : denomexpBy TwoPlusTwoCos32Base (DCos32 ∋ ½) ≡ 16
_ = refl
-- (1 - x)⁶ ≡ -6x + 15x² - 21x³ + 15x⁴ - 6x⁵ (mod x⁶ + x³ + 1), and
-- x³ = ζ₃.
_ : showsPrec-DenomExpNamed {TZeta9} {ZZeta9} OneMinusZeta9Base 0 (⅓″ * (1 - ζ₉))
      ≡ "recip (1 - zeta9)^5 * Cub (Quad 0 (-7)) (Quad (-2) 5) (Quad 5 (-2))"
_ = refl

zeta9-samples : List TZeta9
zeta9-samples =
  map (λ j -> ⅓″ * one-minus-zeta9 ^ j) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []) ++
  map (λ j -> (⅓″ * ⅓″) * one-minus-zeta9 ^ j) (0 ∷ 5 ∷ 9 ∷ []) ++
  (⅓″ * ζ₉ ∷ ⅓″ * (1 + ζ₉ ^ 2) ∷ ⅓″ * (ζ₉ + ζ₉ ^ 4) ∷ Cub 0 ⅓′ (⅓′ * ⅓′) ∷ [])

cos16-samples : List DCos16
cos16-samples =
  map (λ j -> ½ * two-plus-twocos16 ^ j) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []) ++
  (√½ ∷ ½ * twocos16 ∷ ½ * lift-Quad twocos8 ∷ ½ * (1 + twocos16 ^ 3) ∷ [])

roottwo-samples : List DRootTwo
roottwo-samples = concatMap (λ a -> map (λ b -> RootTwo a b) coefficients) coefficients
  where
    coefficients : List Dyadic
    coefficients = 0 ∷ ½ ∷ - ½ ∷ ½ * ½ ∷ 1 ∷ 3 ∷ []

_ : all (check-denominator {TZeta9} {ZZeta9} OneMinusZeta9Base one-minus-zeta9) zeta9-samples ≡ true
_ = refl
_ : all (check-denominator {DCos16} {ZCos16} TwoPlusTwoCos16Base two-plus-twocos16) cos16-samples ≡ true
_ = refl
_ : all (check-denominator {DRootTwo} {ZRootTwo} TwoPlusRootTwoBase two-plus-roottwo) roottwo-samples ≡ true
_ = refl

-- The exponents for different bases: (3) = ξ⁶ in ℤ[ζ₉]; (2) = ξ⁸ and
-- (√2) = ξ⁴ in ℤ[2cos(π/16)]; and (2 + √2) = (√2).
_ : all (λ a -> denomexpBy ThreeBase a == ceil-div (denomexpBy OneMinusZeta9Base a) 6) zeta9-samples ≡ true
_ = refl
_ : all (λ a -> (denomexp a == ceil-div (denomexpBy TwoPlusTwoCos16Base a) 4)
              ∧ (denomexpBy TwoBase a == ceil-div (denomexpBy TwoPlusTwoCos16Base a) 8)) cos16-samples ≡ true
_ = refl
_ : all (λ a -> denomexpBy TwoPlusRootTwoBase a == denomexp a) roottwo-samples ≡ true
_ = refl

-- The valuation formulas agree with a search.
search-zeta9 : DenomExp OneMinusZeta9Base TZeta9
search-zeta9 = denomexp-by-search ThreeBase 6 one-minus-zeta9

search-cos16 : DenomExp TwoPlusTwoCos16Base DCos16
search-cos16 = denomexp-by-search TwoBase 8 two-plus-twocos16

_ : all (λ a -> denomexpBy OneMinusZeta9Base {{search-zeta9}} a == denomexpBy OneMinusZeta9Base a) zeta9-samples ≡ true
_ = refl
_ : all (λ a -> denomexpBy TwoPlusTwoCos16Base {{search-cos16}} a == denomexpBy TwoPlusTwoCos16Base a) cos16-samples ≡ true
_ = refl

-- The qutrit T gate diag(1, ζ₉, ζ₉⁻¹) is unitary and integral.
T3 : SO3 TZeta9
T3 = matrix3x3 (1 , 0 , 0) (0 , ζ₉ , 0) (0 , 0 , ζ₉ ^ 8)

_ : adj T3 * T3 ≡ 1
_ = refl
_ : T3 ^ 9 ≡ 1
_ = refl
_ : denomexpBy OneMinusZeta9Base T3 ≡ 0
_ = refl

-- ℤ[ζ₃₂] and ℤ[2cos(π/32)] have degree 16 over ℤ, three extensions
-- above ℤ[ω] or ℤ[√2], and evaluating their arithmetic in the type
-- checker is expensive (the independent oracle above runs out of
-- memory already for a few elements). Instead, the least exponents of
-- some elements are compared with their known valuations: √2 = ξ⁸u,
-- ζ₃₂ and 2cos(π/32) are units, and 2cos(π/32) and ξ have valuation 1.
_ : denomexpBy OnePlusZeta32Base (DZeta32 ∋ √½) ≡ 8
_ = refl
_ : denomexpBy OnePlusZeta32Base (DZeta32 ∋ ½ * ζ₃₂) ≡ 16
_ = refl
_ : denomexpBy OnePlusZeta32Base (DZeta32 ∋ ½ * one-plus-zeta32) ≡ 15
_ = refl
_ : denomexpBy TwoPlusTwoCos32Base (DCos32 ∋ √½) ≡ 8
_ = refl
_ : denomexpBy TwoPlusTwoCos32Base (DCos32 ∋ ½ * twocos32) ≡ 15
_ = refl
_ : denomexpBy TwoPlusTwoCos32Base (DCos32 ∋ ½ * two-plus-twocos32) ≡ 15
_ = refl
