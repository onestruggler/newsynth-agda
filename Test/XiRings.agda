-- Tests for the ξ-rings of Quantum.Synthesis.Ring.XiRings from Tables
-- 2.1-2.3 of Kliuchnikov–Schönnenbeck (arXiv:2405.19302) that were not
-- already in Quantum.Synthesis.Ring: ℤ[ζ₁₆], ℤ[ζ₃] and ℤ[2cos(π/8)],
-- with ℤ[⅓], checked by evaluation. The towers of Tables 7.1 and 7.2
-- are tested in Test.XiRingsTower.

{-# OPTIONS --without-K --safe #-}

module Test.XiRings where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Integer.Base using (ℤ)
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
open import Quantum.Synthesis.Ring.XiRings
open import Quantum.Synthesis.Matrix hiding (Plus ; Times)

-- ----------------------------------------------------------------------
-- * The rings

-- ζ₁₆ is a primitive 16th root of unity with ζ₁₆² = ω.
_ : (ZZeta16 ∋ ζ₁₆ ^ 2) ≡ ω
_ = refl
_ : (ZZeta16 ∋ ζ₁₆ ^ 8) ≡ -1
_ = refl
_ : (ZZeta16 ∋ ζ₁₆ ^ 16) ≡ 1
_ = refl
_ : (ZZeta16 ∋ adj ζ₁₆ * ζ₁₆) ≡ 1
_ = refl

-- ζ₃ is a primitive cube root of unity, and (1 + 2ζ₃)² = -3.
_ : (ZZeta3 ∋ ζ₃ ^ 2 + ζ₃ + 1) ≡ 0
_ = refl
_ : (ZZeta3 ∋ ζ₃ ^ 3) ≡ 1
_ = refl
_ : (ZZeta3 ∋ adj ζ₃ * ζ₃) ≡ 1
_ = refl
_ : (ZZeta3 ∋ sqrt-minus-three ^ 2) ≡ -3
_ = refl

-- θ = 2cos(π/8) is a real root of x⁴ - 4x² + 2.
_ : (ZCos8 ∋ twocos8 ^ 2) ≡ 2 + √2
_ = refl
_ : (ZCos8 ∋ twocos8 ^ 4 - 4 * twocos8 ^ 2 + 2) ≡ 0
_ = refl
_ : (ZCos8 ∋ adj twocos8) ≡ twocos8
_ = refl

-- ℤ[⅓].
_ : (Triadic ∋ ⅓ * 3) ≡ 1
_ = refl
_ : (Triadic ∋ ⅓ + ⅓ + ⅓) ≡ 1
_ = refl
_ : (Triadic ∋ 2 * ⅓ ^ 2 - ⅓) ≡ - ⅓ * ⅓
_ = refl
_ : show (Triadic ∋ 5 * ⅓ ^ 3) ≡ "5/27"
_ = refl
_ : denomexpBy ThreeBase (Triadic ∋ 6 * ⅓ ^ 3) ≡ 2
_ = refl
_ : denomexp-factorBy ThreeBase (Triadic ∋ 2 * ⅓ ^ 2) 3 ≡ 6
_ = refl

-- ξᵈ is p times a unit u, with u computed by hand:
-- (1 + x)⁸ ≡ 8x + 28x² + 56x³ + 70x⁴ + 56x⁵ + 28x⁶ + 8x⁷ (mod x⁸ + 1),
-- and (2 + θ)⁴ = (70 + 28√2) + (48 + 8√2)θ.
_ : (ZZeta16 ∋ one-plus-zeta16 ^ 8) ≡ 2 * Quad (Omega 14 35 14 0) (Omega 4 28 28 4)
_ = refl
_ : (ZCos8 ∋ two-plus-twocos8 ^ 4) ≡ 2 * Quad (35 + 14 * √2) (24 + 4 * √2)
_ = refl

-- ----------------------------------------------------------------------
-- * Least denominator exponents

-- ⅓ as an element of ℤ[ζ₃, ⅓].
⅓′ : TZeta3
⅓′ = lift-Quad ⅓

_ : denomexpBy OnePlusZeta16Base (DZeta16 ∋ ½) ≡ 8
_ = refl
_ : denomexpBy OnePlusZeta16Base (DZeta16 ∋ √½) ≡ 4
_ = refl
_ : denomexpBy OnePlusZeta16Base (DZeta16 ∋ 3 + ζ₁₆) ≡ 0
_ = refl
_ : denomexp-decomposeBy {DZeta16} {ZZeta16} OnePlusZeta16Base ½ ≡ (Quad (Omega 14 35 14 0) (Omega 4 28 28 4) , 8)
_ = refl
_ : denomexpBy SqrtMinusThreeBase (TZeta3 ∋ ⅓′) ≡ 2
_ = refl
_ : denomexpBy SqrtMinusThreeBase (TZeta3 ∋ ⅓′ * sqrt-minus-three) ≡ 1
_ = refl
_ : denomexp-decomposeBy {TZeta3} {ZZeta3} SqrtMinusThreeBase ⅓′ ≡ (-1 , 2)
_ = refl
_ : denomexpBy TwoPlusTwoCos8Base (DCos8 ∋ ½) ≡ 4
_ = refl
_ : denomexpBy TwoPlusTwoCos8Base (DCos8 ∋ ½ * twocos8) ≡ 3
_ = refl
_ : denomexp-decomposeBy {DCos8} {ZCos8} TwoPlusTwoCos8Base ½ ≡ (Quad (35 + 14 * √2) (24 + 4 * √2) , 4)
_ = refl

-- The coefficient-ring bases lift.
_ : denomexp (DZeta16 ∋ √½ * ζ₁₆) ≡ 1
_ = refl
_ : denomexpBy TwoBase (DCos8 ∋ ½ * twocos8 + ½ ^ 3) ≡ 3
_ = refl
_ : denomexpBy ThreeBase (TZeta3 ∋ ⅓′ ^ 2 * ζ₃) ≡ 2
_ = refl

-- Printing with the default names of the bases.
_ : showsPrec-DenomExpNamed {DZeta16} {ZZeta16} OnePlusZeta16Base 0 ½
      ≡ "recip (1 + zeta16)^8 * Quad (Omega 14 35 14 0) (Omega 4 28 28 4)"
_ = refl
_ : showsPrec-DenomExpNamed {TZeta3} {ZZeta3} SqrtMinusThreeBase 0 ⅓′ ≡ "recip (sqrt (-3))^2 * Quad (-1) 0"
_ = refl
_ : showsPrec-DenomExpNamed {DCos8} {ZCos8} TwoPlusTwoCos8Base 0 ½
      ≡ "recip (2 + 2*cos (pi/8))^4 * Quad (35 + 14*roottwo) (24 + 4*roottwo)"
_ = refl

-- ----------------------------------------------------------------------
-- * Checks on samples

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

  powers : List ℕ
  powers = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []

zeta16-samples : List DZeta16
zeta16-samples =
  map (λ j -> ½ * one-plus-zeta16 ^ j) powers ++
  map (λ j -> ½ * ½ * one-plus-zeta16 ^ j) (0 ∷ 3 ∷ 7 ∷ 12 ∷ []) ++
  map (λ j -> ½ * ζ₁₆ ^ j * (1 + ω)) (0 ∷ 1 ∷ 5 ∷ []) ++
  (0 ∷ 1 ∷ √½ ∷ √½ * ζ₁₆ ∷ ½ * (ζ₁₆ + ω) ∷ ½ * (1 + ζ₁₆ ^ 3) ∷ Quad (Omega ½ 0 0 0) (Omega 0 0 0 (½ * ½)) ∷ [])

zeta3-samples : List TZeta3
zeta3-samples =
  map (λ j -> ⅓′ * sqrt-minus-three ^ j) (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ++
  map (λ j -> ⅓′ * ⅓′ * sqrt-minus-three ^ j) (0 ∷ 1 ∷ 3 ∷ []) ++
  concatMap (λ a -> map (λ b -> Quad a b) coefficients) coefficients
  where
    coefficients : List Triadic
    coefficients = 0 ∷ ⅓ ∷ - ⅓ ∷ 2 * ⅓ ∷ ⅓ * ⅓ ∷ 1 ∷ []

cos8-samples : List DCos8
cos8-samples =
  map (λ j -> ½ * two-plus-twocos8 ^ j) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ++
  map (λ j -> ½ * ½ * two-plus-twocos8 ^ j) (0 ∷ 1 ∷ 5 ∷ []) ++
  concatMap (λ a -> concatMap (λ b -> concatMap (λ c -> map (λ d ->
    Quad (RootTwo a b) (RootTwo c d)) halves) halves) halves) halves
  where
    halves : List Dyadic
    halves = 0 ∷ ½ ∷ []

_ : all (check-denominator {DZeta16} {ZZeta16} OnePlusZeta16Base one-plus-zeta16) zeta16-samples ≡ true
_ = refl
_ : all (check-denominator {TZeta3} {ZZeta3} SqrtMinusThreeBase sqrt-minus-three) zeta3-samples ≡ true
_ = refl
_ : all (check-denominator {DCos8} {ZCos8} TwoPlusTwoCos8Base two-plus-twocos8) cos8-samples ≡ true
_ = refl

-- The exponents for different bases: (√2) = ξ⁴ and (2) = ξ⁸ in ℤ[ζ₁₆];
-- (3) = ξ² in ℤ[ζ₃]; (√2) = ξ² and (2) = ξ⁴ in ℤ[2cos(π/8)].
_ : all (λ a -> (denomexp a == ceil-div (denomexpBy OnePlusZeta16Base a) 4)
              ∧ (denomexpBy TwoBase a == ceil-div (denomexpBy OnePlusZeta16Base a) 8)) zeta16-samples ≡ true
_ = refl
_ : all (λ a -> denomexpBy ThreeBase a == ceil-div (denomexpBy SqrtMinusThreeBase a) 2) zeta3-samples ≡ true
_ = refl
_ : all (λ a -> (denomexp a == ceil-div (denomexpBy TwoPlusTwoCos8Base a) 2)
              ∧ (denomexpBy TwoBase a == ceil-div (denomexpBy TwoPlusTwoCos8Base a) 4)) cos8-samples ≡ true
_ = refl

-- The valuation formulas agree with a search ((1 + ζ₁₆)⁸ = 2u, (√-3)² = -3).
search-zeta16 : DenomExp OnePlusZeta16Base DZeta16
search-zeta16 = denomexp-by-search TwoBase 8 one-plus-zeta16

search-zeta3 : DenomExp SqrtMinusThreeBase TZeta3
search-zeta3 = denomexp-by-search ThreeBase 2 sqrt-minus-three

_ : all (λ a -> denomexpBy OnePlusZeta16Base {{search-zeta16}} a == denomexpBy OnePlusZeta16Base a) zeta16-samples ≡ true
_ = refl
_ : all (λ a -> denomexpBy SqrtMinusThreeBase {{search-zeta3}} a == denomexpBy SqrtMinusThreeBase a) zeta3-samples ≡ true
_ = refl

-- ----------------------------------------------------------------------
-- * Gates of Table 2.3

-- √T = diag(1, ζ₁₆) is unitary, squares to T, and is integral.
sqrtT : U2 DZeta16
sqrtT = matrix2x2 (1 , 0) (0 , ζ₁₆)

_ : adj sqrtT * sqrtT ≡ 1
_ = refl
_ : sqrtT * sqrtT ≡ matrix2x2 (1 , 0) (0 , ω)
_ = refl
_ : denomexpBy OnePlusZeta16Base sqrtT ≡ 0
_ = refl
_ : denomexpBy OnePlusZeta16Base (U2 DZeta16 ∋ matrix2x2 (√½ , √½) (√½ , - √½)) ≡ 4
_ = refl

-- T_y, the rotation by π/8 (cos(π/8) = θ/2, sin(π/8) = (√2 - 1)θ/2),
-- is orthogonal, squares to the rotation by π/4, and has least
-- (2 + 2cos(π/8))-exponent 3.
Ty : U2 DCos8
Ty = matrix2x2 (c , - s) (s , c)
  where
    c s : DCos8
    c = ½ * twocos8
    s = ½ * (√2 - 1) * twocos8

_ : adj Ty * Ty ≡ 1
_ = refl
_ : Ty * Ty ≡ matrix2x2 (√½ , - √½) (√½ , √½)
_ = refl
_ : denomexpBy TwoPlusTwoCos8Base Ty ≡ 3
_ = refl

-- The qutrit Hadamard (1/√-3)[[1,1,1],[1,ζ₃,ζ₃²],[1,ζ₃²,ζ₃]] is
-- unitary and has least √-3-exponent 1.
H3 : SO3 TZeta3
H3 = matrix-map (λ x -> r * x) (matrix3x3 (1 , 1 , 1) (1 , ζ₃ , ζ₃ ^ 2) (1 , ζ₃ ^ 2 , ζ₃))
  where
    -- 1/√-3 = -√-3/3.
    r : TZeta3
    r = - ⅓′ * sqrt-minus-three

_ : adj H3 * H3 ≡ 1
_ = refl
_ : denomexpBy SqrtMinusThreeBase H3 ≡ 1
_ = refl
