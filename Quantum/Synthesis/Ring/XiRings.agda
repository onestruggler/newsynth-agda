-- The concrete global ξ-rings of Kliuchnikov and Schönnenbeck,
-- "Multi-qubit circuit synthesis and Hermitian lattices"
-- (arXiv:2405.19302), and their least denominator exponents with
-- respect to the denominator ξ. A ξ-ring is ℛξ = {z/ξᵏ : z ∈ 𝒪, k ∈ ℕ},
-- where ξ generates a prime ideal of the ring of integers 𝒪 with
-- (ξ)ᵈ = (p) for a rational prime p (their Definition 2.3).
--
--   field E          𝒪             ξ              p  d   carrier, tag                where
--   ℚ                ℤ             2              2  1   Dyadic, TwoBase            T7.1
--   ℚ(i)             ℤ[i]          1 + i          2  2   DComplex, OnePlusIBase     T2.1-2.3, T4.1
--   ℚ(√2)            ℤ[√2]         √2             2  2   DRootTwo, SqrtTwoBase      T2.1-2.3, T4.1
--   ℚ(√2)            ℤ[√2]         2 + √2         2  2   DRootTwo, TwoPlusRootTwoBase T7.1 (m = 3)
--   ℚ(ζ₈)            ℤ[ζ₈]         1 + ζ₈         2  4   DOmega, OnePlusOmegaBase   T2.1-2.3, T4.1, T7.1
--   ℚ(ζ₁₆)           ℤ[ζ₁₆]        1 + ζ₁₆        2  8   DZeta16, OnePlusZeta16Base T2.1, T2.3, T7.1
--   ℚ(ζ₃₂)           ℤ[ζ₃₂]        1 + ζ₃₂        2  16  DZeta32, OnePlusZeta32Base T7.1, T7.2
--   ℚ(cos(π/8))      ℤ[2cos(π/8)]  2 + 2cos(π/8)  2  4   DCos8, TwoPlusTwoCos8Base  T2.3, T4.1, T7.1
--   ℚ(cos(π/16))     ℤ[2cos(π/16)] 2 + 2cos(π/16) 2  8   DCos16, TwoPlusTwoCos16Base T7.1
--   ℚ(cos(π/32))     ℤ[2cos(π/32)] 2 + 2cos(π/32) 2  16  DCos32, TwoPlusTwoCos32Base T7.1
--   ℚ(ζ₃)            ℤ[ζ₃]         √-3            3  2   TZeta3, SqrtMinusThreeBase T2.1, T2.2, T7.2
--   ℚ(ζ₉)            ℤ[ζ₉]         1 - ζ₉         3  6   TZeta9, OneMinusZeta9Base  T7.2
--
-- (Tables 7.1 use ξ = 1 + ζ_{2^m} and 2 + 2cos(2π/2^m); the paper
-- does not name a denominator for ℚ(ζ₉), and 1 - ζ₉ is the usual
-- generator of the prime over 3. Table 4.1 writes 2 + 2cos(π/16) for
-- ℚ(cos(π/8)), which is not in that field; Tables 2.3 and 7.1 give
-- 2 + 2cos(π/8).) The first five are in Quantum.Synthesis.Ring. The
-- new rings of integers are built as towers of extensions
-- (Quantum.Synthesis.Ring.Quadratic and .Cubic) of rings that are
-- already there:
--
--   ℤ[ζ₁₆] = ℤ[ω][θ], θ² = ω        ℤ[ζ₃₂] = ℤ[ζ₁₆][θ], θ² = ζ₁₆
--   ℤ[ζ₃] = ℤ[θ], θ² = -1 - θ       ℤ[ζ₉] = ℤ[ζ₃][θ], θ³ = ζ₃
--   ℤ[2cos(π/8)] = ℤ[√2][θ], θ² = 2 + √2
--   ℤ[2cos(π/2ᵏ⁺¹)] = ℤ[2cos(π/2ᵏ)][θ], θ² = 2 + 2cos(π/2ᵏ)
--
-- and the ξ-rings are obtained by inverting p in the coefficients
-- (e.g. ℤ[ζ₃, 1/√-3] = ℤ[⅓][ζ₃]), since ξᵈ is p times a unit.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.XiRings where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.List.Base using (List ; [] ; _∷_ ; map ; reverse)
open import Data.Nat.Base as Nat using (ℕ ; zero ; suc)
open import Data.Integer.Base as Int using (ℤ)
open import Data.Product.Base using (_×_ ; _,_)

open import Instances
open import Literals
open import Quantum.Synthesis.Ring
open import Quantum.Synthesis.Ring.Localized
open import Quantum.Synthesis.Ring.Quadratic
open import Quantum.Synthesis.Ring.Cubic

-- ----------------------------------------------------------------------
-- * Generators

-- ζ₁₆ over a ring containing ω = ζ₈: ζ₁₆² = ω.
data Zeta16 : Set where
-- ζ₃ = e^{2πi/3}: ζ₃² = -1 - ζ₃.
data Zeta3 : Set where
-- ζ₉ over ℤ[ζ₃]: ζ₉³ = ζ₃.
data Zeta9 : Set where
-- 2cos(π/8) = √(2 + √2) over a ring containing √2: θ² = 2 + √2.
data TwoCos8 : Set where
-- The square root of the generator of an extension G, e.g. ζ₃₂ = √ζ₁₆.
data SqrtGen (G : Set) : Set where
-- 2cos(φ/2) = √(2 + 2cos φ), where 2cos φ is the generator of G.
data TwoCosHalf (G : Set) : Set where

Zeta32 TwoCos16 TwoCos32 : Set
Zeta32 = SqrtGen Zeta16
TwoCos16 = TwoCosHalf TwoCos8
TwoCos32 = TwoCosHalf TwoCos16

instance
  GeneratorZeta16 : {A : Set} {{_ : Ring A}} {{_ : OmegaRing A}} -> Generator Zeta16 A
  GeneratorZeta16 .gen-s = omega
  GeneratorZeta16 .gen-t = 0#

  GeneratorZeta3 : {A : Set} {{_ : Ring A}} -> Generator Zeta3 A
  GeneratorZeta3 .gen-s = - 1#
  GeneratorZeta3 .gen-t = - 1#

  GeneratorTwoCos8 : {A : Set} {{_ : Ring A}} {{_ : RootTwoRing A}} -> Generator TwoCos8 A
  GeneratorTwoCos8 .gen-s = 1# + 1# + roottwo
  GeneratorTwoCos8 .gen-t = 0#

  GeneratorSqrtGen : {G B : Set} {{_ : Ring B}} {{_ : Generator G B}} -> Generator (SqrtGen G) (Quadratic G B)
  GeneratorSqrtGen .gen-s = generator
  GeneratorSqrtGen .gen-t = 0#

  GeneratorTwoCosHalf : {G B : Set} {{_ : Ring B}} {{_ : Generator G B}} -> Generator (TwoCosHalf G) (Quadratic G B)
  GeneratorTwoCosHalf .gen-s = 1# + 1# + generator
  GeneratorTwoCosHalf .gen-t = 0#

  CubicGeneratorZeta9 : {B : Set} {{_ : Ring B}} -> CubicGenerator Zeta9 (Quadratic Zeta3 B)
  CubicGeneratorZeta9 .cubic-s = generator

  -- Complex conjugation. The roots of unity have adj ζ = ζ⁻¹, so that
  -- adj ζ₁₆ = -ω³ζ₁₆, adj ζ₃ = ζ₃² = -1 - ζ₃, adj √ζ = adj ζ · √ζ and
  -- adj ζ₉ = adj ζ₃ · ζ₉². The cosines are real.
  AdjointGeneratorZeta16 : {A : Set} {{_ : Ring A}} {{_ : OmegaRing A}} -> AdjointGenerator Zeta16 A
  AdjointGeneratorZeta16 .gen-adj-u = 0#
  AdjointGeneratorZeta16 .gen-adj-v = - omega ^ 3

  AdjointGeneratorZeta3 : {A : Set} {{_ : Ring A}} -> AdjointGenerator Zeta3 A
  AdjointGeneratorZeta3 .gen-adj-u = - 1#
  AdjointGeneratorZeta3 .gen-adj-v = - 1#

  AdjointGeneratorTwoCos8 : {A : Set} {{_ : Ring A}} -> AdjointGenerator TwoCos8 A
  AdjointGeneratorTwoCos8 .gen-adj-u = 0#
  AdjointGeneratorTwoCos8 .gen-adj-v = 1#

  AdjointGeneratorSqrtGen : {G B : Set} {{_ : Ring B}} {{_ : Generator G B}} {{_ : Adjoint B}} {{_ : AdjointGenerator G B}}
    -> AdjointGenerator (SqrtGen G) (Quadratic G B)
  AdjointGeneratorSqrtGen .gen-adj-u = 0#
  AdjointGeneratorSqrtGen .gen-adj-v = adj generator

  AdjointGeneratorTwoCosHalf : {G B : Set} {{_ : Ring B}} {{_ : Generator G B}} -> AdjointGenerator (TwoCosHalf G) (Quadratic G B)
  AdjointGeneratorTwoCosHalf .gen-adj-u = 0#
  AdjointGeneratorTwoCosHalf .gen-adj-v = 1#

  AdjointCubicGeneratorZeta9 : {B : Set} {{_ : Ring B}} {{_ : Adjoint B}} -> AdjointCubicGenerator Zeta9 (Quadratic Zeta3 B)
  AdjointCubicGeneratorZeta9 .cubic-adj-u₀ = 0#
  AdjointCubicGeneratorZeta9 .cubic-adj-u₁ = 0#
  AdjointCubicGeneratorZeta9 .cubic-adj-u₂ = adj generator

infixl 20 _[ζ₁₆] _[ζ₃₂] _[ζ₃] _[ζ₉] _[2cosπ/8] _[2cosπ/16] _[2cosπ/32]

_[ζ₁₆] _[ζ₃₂] _[ζ₃] _[ζ₉] _[2cosπ/8] _[2cosπ/16] _[2cosπ/32] : Set -> Set
A [ζ₁₆] = Quadratic Zeta16 A
A [ζ₃₂] = Quadratic Zeta32 A
A [ζ₃] = Quadratic Zeta3 A
A [ζ₉] = Cubic Zeta9 A
A [2cosπ/8] = Quadratic TwoCos8 A
A [2cosπ/16] = Quadratic TwoCos16 A
A [2cosπ/32] = Quadratic TwoCos32 A

zeta16 ζ₁₆ : {A : Set} {{_ : Ring A}} -> A [ζ₁₆]
zeta16 = generator
ζ₁₆ = zeta16

zeta32 ζ₃₂ : {A : Set} {{_ : Ring A}} -> A [ζ₃₂]
zeta32 = generator
ζ₃₂ = zeta32

zeta3 ζ₃ : {A : Set} {{_ : Ring A}} -> A [ζ₃]
zeta3 = generator
ζ₃ = zeta3

zeta9 ζ₉ : {A : Set} {{_ : Ring A}} -> A [ζ₉]
zeta9 = cubic-generator
ζ₉ = zeta9

-- 2cos(π/8), 2cos(π/16) and 2cos(π/32).
twocos8 : {A : Set} {{_ : Ring A}} -> A [2cosπ/8]
twocos8 = generator

twocos16 : {A : Set} {{_ : Ring A}} -> A [2cosπ/16]
twocos16 = generator

twocos32 : {A : Set} {{_ : Ring A}} -> A [2cosπ/32]
twocos32 = generator

-- ----------------------------------------------------------------------
-- * The rings

-- 2-power cyclotomic integers, and the same with ½.
ZZeta16 ℤ[ζ₁₆] DZeta16 𝔻[ζ₁₆] ZZeta32 ℤ[ζ₃₂] DZeta32 𝔻[ζ₃₂] : Set
ZZeta16 = ZOmega [ζ₁₆]
ℤ[ζ₁₆] = ZZeta16
DZeta16 = DOmega [ζ₁₆]
𝔻[ζ₁₆] = DZeta16
ZZeta32 = ZZeta16 [ζ₃₂]
ℤ[ζ₃₂] = ZZeta32
DZeta32 = DZeta16 [ζ₃₂]
𝔻[ζ₃₂] = DZeta32

-- 3-power cyclotomic integers (ℤ[ζ₃] = the Eisenstein integers), and
-- the same with ⅓.
ZZeta3 ℤ[ζ₃] TZeta3 ℤ[ζ₃,⅓] ZZeta9 ℤ[ζ₉] TZeta9 ℤ[ζ₉,⅓] : Set
ZZeta3 = ℤ [ζ₃]
ℤ[ζ₃] = ZZeta3
TZeta3 = Triadic [ζ₃]
ℤ[ζ₃,⅓] = TZeta3
ZZeta9 = ZZeta3 [ζ₉]
ℤ[ζ₉] = ZZeta9
TZeta9 = TZeta3 [ζ₉]
ℤ[ζ₉,⅓] = TZeta9

-- The integers of the real subfields ℚ(cos(π/2ᵏ)), and the same with ½.
ZCos8 ℤ[2cosπ/8] DCos8 𝔻[2cosπ/8] ZCos16 ℤ[2cosπ/16] DCos16 𝔻[2cosπ/16] : Set
ZCos8 = ZRootTwo [2cosπ/8]
ℤ[2cosπ/8] = ZCos8
DCos8 = DRootTwo [2cosπ/8]
𝔻[2cosπ/8] = DCos8
ZCos16 = ZCos8 [2cosπ/16]
ℤ[2cosπ/16] = ZCos16
DCos16 = DCos8 [2cosπ/16]
𝔻[2cosπ/16] = DCos16

ZCos32 ℤ[2cosπ/32] DCos32 𝔻[2cosπ/32] : Set
ZCos32 = ZCos16 [2cosπ/32]
ℤ[2cosπ/32] = ZCos32
DCos32 = DCos16 [2cosπ/32]
𝔻[2cosπ/32] = DCos32

-- ----------------------------------------------------------------------
-- * Coordinates in a power basis

-- The integer coordinates of a whole element in the power basis
-- 1, θ, θ², ... of the generator θ at the top of its tower (lowest
-- degree first). For a quadratic step θ² = φ (and θ³ = φ for the
-- cubic step), where φ is the generator below, this interleaves the
-- coordinates of the two (three) components. The towers above satisfy
-- this exactly, except for the cosines, where θ² = 2 + φ ≡ φ, so that
-- the coordinates are correct modulo 2, which is all we use.
record PowerBasis (A : Set) : Set where
  field
    power-coeffs : A -> List ℤ
open PowerBasis {{...}} public

interleave : List ℤ -> List ℤ -> List ℤ
interleave (x ∷ xs) (y ∷ ys) = x ∷ y ∷ interleave xs ys
interleave xs [] = xs
interleave [] ys = ys

interleave3 : List ℤ -> List ℤ -> List ℤ -> List ℤ
interleave3 (x ∷ xs) (y ∷ ys) (z ∷ zs) = x ∷ y ∷ z ∷ interleave3 xs ys zs
interleave3 _ _ _ = []

instance
  PowerBasisℤ : PowerBasis ℤ
  PowerBasisℤ .power-coeffs a = a ∷ []

  -- a + b√2, with √2 = 2cos(π/4).
  PowerBasisZRootTwo : PowerBasis ZRootTwo
  PowerBasisZRootTwo .power-coeffs (RootTwo a b) = a ∷ b ∷ []

  PowerBasisZOmega : PowerBasis ZOmega
  PowerBasisZOmega .power-coeffs (Omega a b c d) = d ∷ c ∷ b ∷ a ∷ []

  PowerBasisQuad : {G B : Set} {{_ : PowerBasis B}} -> PowerBasis (Quadratic G B)
  PowerBasisQuad .power-coeffs (Quad x y) = interleave (power-coeffs x) (power-coeffs y)

  PowerBasisCub : {G B : Set} {{_ : PowerBasis B}} -> PowerBasis (Cubic G B)
  PowerBasisCub .power-coeffs (Cub x y z) = interleave3 (power-coeffs x) (power-coeffs y) (power-coeffs z)

-- ----------------------------------------------------------------------
-- * Valuations at ξ

private
  -- Divide a polynomial over 𝔽ₚ (residues, the highest degree first,
  -- the leading one being the second argument) by x - 1: return the
  -- quotient and the remainder, which is the value at 1.
  div-x-1 : ℕ -> ℕ -> List ℕ -> List ℕ × ℕ
  div-x-1 p b [] = [] , b
  div-x-1 p b (c ∷ cs) with div-x-1 p ((c Nat.+ b) Nat.% pos p) cs
  ... | q , r = b ∷ q , r

  -- The multiplicity of the factor x - 1 in a non-zero polynomial over
  -- 𝔽ₚ (the second argument is fuel).
  mult-x-1 : ℕ -> ℕ -> List ℕ -> ℕ
  mult-x-1 p zero _ = zero
  mult-x-1 p (suc f) [] = zero
  mult-x-1 p (suc f) (c ∷ cs) with div-x-1 p c cs
  ... | q , zero = suc (mult-x-1 p f q)
  ... | q , suc _ = zero

  -- The index of the first odd entry.
  first-odd : List ℤ -> ℕ
  first-odd [] = zero
  first-odd (a ∷ as) = if evenℤ a then suc (first-odd as) else zero

-- The valuation, at ξ, of whole elements that p does not divide.
--
-- Cyclotomic: ℤ[ζ]/(p) = 𝔽ₚ[x]/(Φ(x)) with Φ ≡ (x - 1)ᵈ (mod p) for
-- ζ of order a power of p, and ξ is an associate of ζ - 1 (1 + ζ for
-- p = 2; √-3 = ζ₃(1 - ζ₃)). So ν is the multiplicity of x - 1 in the
-- coordinates of the element modulo p (at most d - 1, since p does not
-- divide the element; d is the fuel).
nu-cyclotomic : {B : Set} {{_ : PowerBasis B}} -> ℕ -> ℕ -> B -> ℕ
nu-cyclotomic p d x = mult-x-1 p d (reverse (map (λ a -> a Int.%ℕ pos p) (power-coeffs x)))

-- Real: θ = 2cos(π/2ᵏ) and 2 + θ both have norm ±2, so they generate
-- the prime over 2, with residue field 𝔽₂. So ν is the index of the
-- first odd coordinate in the power basis of θ.
nu-real : {B : Set} {{_ : PowerBasis B}} -> B -> ℕ
nu-real x = first-odd (power-coeffs x)

-- ----------------------------------------------------------------------
-- * The denominators ξ

data OnePlusZeta16Base : Set where
data OnePlusZeta32Base : Set where
data SqrtMinusThreeBase : Set where
data OneMinusZeta9Base : Set where
data TwoPlusTwoCos8Base : Set where
data TwoPlusTwoCos16Base : Set where
data TwoPlusTwoCos32Base : Set where
data TwoPlusRootTwoBase : Set where

one-plus-zeta16 : {A : Set} {{_ : Ring A}} -> A [ζ₁₆]
one-plus-zeta16 = Quad 1# 1#

one-plus-zeta32 : {A : Set} {{_ : Ring A}} -> A [ζ₃₂]
one-plus-zeta32 = Quad 1# 1#

-- √-3 = 1 + 2ζ₃.
sqrt-minus-three : {A : Set} {{_ : Ring A}} -> A [ζ₃]
sqrt-minus-three = Quad 1# (1# + 1#)

one-minus-zeta9 : {A : Set} {{_ : Ring A}} -> A [ζ₉]
one-minus-zeta9 = Cub 1# (- 1#) 0#

two-plus-twocos8 : {A : Set} {{_ : Ring A}} -> A [2cosπ/8]
two-plus-twocos8 = Quad (1# + 1#) 1#

two-plus-twocos16 : {A : Set} {{_ : Ring A}} -> A [2cosπ/16]
two-plus-twocos16 = Quad (1# + 1#) 1#

two-plus-twocos32 : {A : Set} {{_ : Ring A}} -> A [2cosπ/32]
two-plus-twocos32 = Quad (1# + 1#) 1#

two-plus-roottwo : DRootTwo
two-plus-roottwo = 1# + 1# + roottwo

instance
  DenomExpDZeta16 : DenomExp OnePlusZeta16Base DZeta16
  DenomExpDZeta16 = denomexp-ramified TwoBase {DZeta16} {ZZeta16} 8 (nu-cyclotomic 2 8) (λ a k -> a * one-plus-zeta16 ^ k)

  DenomExpDZeta32 : DenomExp OnePlusZeta32Base DZeta32
  DenomExpDZeta32 = denomexp-ramified TwoBase {DZeta32} {ZZeta32} 16 (nu-cyclotomic 2 16) (λ a k -> a * one-plus-zeta32 ^ k)

  DenomExpTZeta3 : DenomExp SqrtMinusThreeBase TZeta3
  DenomExpTZeta3 = denomexp-ramified ThreeBase {TZeta3} {ZZeta3} 2 (nu-cyclotomic 3 2) (λ a k -> a * sqrt-minus-three ^ k)

  DenomExpTZeta9 : DenomExp OneMinusZeta9Base TZeta9
  DenomExpTZeta9 = denomexp-ramified ThreeBase {TZeta9} {ZZeta9} 6 (nu-cyclotomic 3 6) (λ a k -> a * one-minus-zeta9 ^ k)

  DenomExpDCos8 : DenomExp TwoPlusTwoCos8Base DCos8
  DenomExpDCos8 = denomexp-ramified TwoBase {DCos8} {ZCos8} 4 nu-real (λ a k -> a * two-plus-twocos8 ^ k)

  DenomExpDCos16 : DenomExp TwoPlusTwoCos16Base DCos16
  DenomExpDCos16 = denomexp-ramified TwoBase {DCos16} {ZCos16} 8 nu-real (λ a k -> a * two-plus-twocos16 ^ k)

  DenomExpDCos32 : DenomExp TwoPlusTwoCos32Base DCos32
  DenomExpDCos32 = denomexp-ramified TwoBase {DCos32} {ZCos32} 16 nu-real (λ a k -> a * two-plus-twocos32 ^ k)

  -- 2 + √2 = √2(1 + √2) is an associate of √2.
  DenomExpDRootTwoTwoPlusRootTwo : DenomExp TwoPlusRootTwoBase DRootTwo
  DenomExpDRootTwoTwoPlusRootTwo = denomexp-ramified TwoBase {DRootTwo} {ZRootTwo} 2 nu-real (λ a k -> a * two-plus-roottwo ^ k)

  BaseNameOnePlusZeta16 : BaseName OnePlusZeta16Base
  BaseNameOnePlusZeta16 .recip-name = "recip (1 + zeta16)"
  BaseNameOnePlusZeta16 .latex-name p = showParen p 6 "1+\\zeta_{16}"

  BaseNameOnePlusZeta32 : BaseName OnePlusZeta32Base
  BaseNameOnePlusZeta32 .recip-name = "recip (1 + zeta32)"
  BaseNameOnePlusZeta32 .latex-name p = showParen p 6 "1+\\zeta_{32}"

  BaseNameSqrtMinusThree : BaseName SqrtMinusThreeBase
  BaseNameSqrtMinusThree .recip-name = "recip (sqrt (-3))"
  BaseNameSqrtMinusThree .latex-name _ = "\\sqrt{-3}"

  BaseNameOneMinusZeta9 : BaseName OneMinusZeta9Base
  BaseNameOneMinusZeta9 .recip-name = "recip (1 - zeta9)"
  BaseNameOneMinusZeta9 .latex-name p = showParen p 6 "1-\\zeta_{9}"

  BaseNameTwoPlusTwoCos8 : BaseName TwoPlusTwoCos8Base
  BaseNameTwoPlusTwoCos8 .recip-name = "recip (2 + 2*cos (pi/8))"
  BaseNameTwoPlusTwoCos8 .latex-name p = showParen p 6 "2+2\\cos(\\pi/8)"

  BaseNameTwoPlusTwoCos16 : BaseName TwoPlusTwoCos16Base
  BaseNameTwoPlusTwoCos16 .recip-name = "recip (2 + 2*cos (pi/16))"
  BaseNameTwoPlusTwoCos16 .latex-name p = showParen p 6 "2+2\\cos(\\pi/16)"

  BaseNameTwoPlusTwoCos32 : BaseName TwoPlusTwoCos32Base
  BaseNameTwoPlusTwoCos32 .recip-name = "recip (2 + 2*cos (pi/32))"
  BaseNameTwoPlusTwoCos32 .latex-name p = showParen p 6 "2+2\\cos(\\pi/32)"

  BaseNameTwoPlusRootTwo : BaseName TwoPlusRootTwoBase
  BaseNameTwoPlusRootTwo .recip-name = "recip (2 + roottwo)"
  BaseNameTwoPlusRootTwo .latex-name p = showParen p 6 "2+\\sqrt{2}"
