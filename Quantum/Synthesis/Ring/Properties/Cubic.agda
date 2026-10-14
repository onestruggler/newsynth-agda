-- If A is a commutative ring, then so is every pure cubic extension
-- Cubic G A = A[θ], θ³ = s (with the ring operations of the instances
-- in Quantum.Synthesis.Ring.Cubic), for all generators G at once. The
-- proof is the one of Properties.Quadratic, with s as a further
-- variable of the polynomials.

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties.Cubic where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong₂ ; cong ; sym ; trans ; module ≡-Reasoning)

open import Instances
open import Quantum.Synthesis.Ring.Cubic
  using (Cubic ; Cub ; CubicGenerator ; cubic-s ; SemiRingCub ; RingCub ; lift-Cub)
open import Quantum.Synthesis.Ring.Properties.Common using (CRLaws ; isCommutativeRing-from-laws)
import Quantum.Synthesis.Ring.Properties.Poly as Poly
import Quantum.Synthesis.Ring.Properties.Hom as Hom

open Cubic using (c-a ; c-b ; c-c)

module _ {G A : Set} {{RA : Ring A}} {{GA : CubicGenerator G A}}
         (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) where
  open Poly isCR using (Polynomial ; var ; ⟦_⟧ ; ⟦_⟧↓ ; prove ; SemiRingPoly ; RingPoly)

  private
    v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ : Polynomial 10
    v₀ = var zero
    v₁ = var (suc zero)
    v₂ = var (suc (suc zero))
    v₃ = var (suc (suc (suc zero)))
    v₄ = var (suc (suc (suc (suc zero))))
    v₅ = var (suc (suc (suc (suc (suc zero)))))
    v₆ = var (suc (suc (suc (suc (suc (suc zero))))))
    v₇ = var (suc (suc (suc (suc (suc (suc (suc zero)))))))
    v₈ = var (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    v₉ = var (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

    -- Over polynomials, s is the variable v₉.
    instance
      CubicGeneratorPoly : CubicGenerator G (Polynomial 10)
      CubicGeneratorPoly = record { cubic-s = v₉ }

    ⟦_⟧C : Cubic G (Polynomial 10) -> Vec A 10 -> Cubic G A
    ⟦ Cub a b c ⟧C ρ = Cub (⟦ a ⟧ ρ) (⟦ b ⟧ ρ) (⟦ c ⟧ ρ)

    by : ∀ (ρ : Vec A 10) (e₁ e₂ : Cubic G (Polynomial 10)) ->
         ⟦ c-a e₁ ⟧↓ ρ ≡ ⟦ c-a e₂ ⟧↓ ρ -> ⟦ c-b e₁ ⟧↓ ρ ≡ ⟦ c-b e₂ ⟧↓ ρ -> ⟦ c-c e₁ ⟧↓ ρ ≡ ⟦ c-c e₂ ⟧↓ ρ ->
         ⟦ e₁ ⟧C ρ ≡ ⟦ e₂ ⟧C ρ
    by ρ (Cub a b c) (Cub a' b' c') h₁ h₂ h₃ = Cub-cong (prove ρ a a' h₁) (prove ρ b b' h₂) (prove ρ c c' h₃)
      where
        Cub-cong : ∀ {x x' y y' z z' : A} -> x ≡ x' -> y ≡ y' -> z ≡ z' -> Cub {G} x y z ≡ Cub x' y' z'
        Cub-cong refl refl refl = refl

    X Y Z : Cubic G (Polynomial 10)
    X = Cub v₀ v₁ v₂
    Y = Cub v₃ v₄ v₅
    Z = Cub v₆ v₇ v₈

    ρ : Cubic G A -> Cubic G A -> Cubic G A -> Vec A 10
    ρ (Cub a b c) (Cub d e f) (Cub g h k) = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ k ∷ cubic-s {G} ∷ []

  +-assoc-Cub : ∀ (x y z : Cubic G A) -> (x + y) + z ≡ x + (y + z)
  +-assoc-Cub x y z = by (ρ x y z) ((X + Y) + Z) (X + (Y + Z)) refl refl refl

  +-comm-Cub : ∀ (x y : Cubic G A) -> x + y ≡ y + x
  +-comm-Cub x y = by (ρ x y y) (X + Y) (Y + X) refl refl refl

  +-identityˡ-Cub : ∀ (x : Cubic G A) -> 0# + x ≡ x
  +-identityˡ-Cub x = by (ρ x x x) (0# + X) X refl refl refl

  -‿inverseˡ-Cub : ∀ (x : Cubic G A) -> (- x) + x ≡ 0#
  -‿inverseˡ-Cub x = by (ρ x x x) ((- X) + X) 0# refl refl refl

  *-comm-Cub : ∀ (x y : Cubic G A) -> x * y ≡ y * x
  *-comm-Cub x y = by (ρ x y y) (X * Y) (Y * X) refl refl refl

  *-identityˡ-Cub : ∀ (x : Cubic G A) -> 1# * x ≡ x
  *-identityˡ-Cub x = by (ρ x x x) (1# * X) X refl refl refl

  distribʳ-Cub : ∀ (x y z : Cubic G A) -> (y + z) * x ≡ y * x + z * x
  distribʳ-Cub x y z = by (ρ x y z) ((Y + Z) * X) (Y * X + Z * X) refl refl refl

  -- Associativity in one step would make the solver normalise
  -- polynomials of degree 5 in 10 variables, which exhausts memory.
  -- Instead, split the first factor into its three coordinates, using
  -- distributivity; associativity for each part is a small problem.
  private
    part₀ part₁ part₂ : Cubic G A -> Cubic G A
    part₀ (Cub a b c) = Cub a 0# 0#
    part₁ (Cub a b c) = Cub 0# b 0#
    part₂ (Cub a b c) = Cub 0# 0# c

    split : ∀ x -> x ≡ part₀ x + (part₁ x + part₂ x)
    split x = by (ρ x x x) X (Cub v₀ 0# 0# + (Cub 0# v₁ 0# + Cub 0# 0# v₂)) refl refl refl

    assoc₀ : ∀ x y z -> (part₀ x * y) * z ≡ part₀ x * (y * z)
    assoc₀ x y z = by (ρ x y z) ((X₀ * Y) * Z) (X₀ * (Y * Z)) refl refl refl
      where X₀ = Cub v₀ 0# 0#

    assoc₁ : ∀ x y z -> (part₁ x * y) * z ≡ part₁ x * (y * z)
    assoc₁ x y z = by (ρ x y z) ((X₁ * Y) * Z) (X₁ * (Y * Z)) refl refl refl
      where X₁ = Cub 0# v₁ 0#

    assoc₂ : ∀ x y z -> (part₂ x * y) * z ≡ part₂ x * (y * z)
    assoc₂ x y z = by (ρ x y z) ((X₂ * Y) * Z) (X₂ * (Y * Z)) refl refl refl
      where X₂ = Cub 0# 0# v₂

    -- (x₀ + (x₁ + x₂)) * w ≡ x₀ * w + (x₁ * w + x₂ * w).
    distrib₃ : ∀ x₀ x₁ x₂ w -> (x₀ + (x₁ + x₂)) * w ≡ x₀ * w + (x₁ * w + x₂ * w)
    distrib₃ x₀ x₁ x₂ w = trans (distribʳ-Cub w x₀ (x₁ + x₂)) (cong (x₀ * w +_) (distribʳ-Cub w x₁ x₂))

  *-assoc-Cub : ∀ (x y z : Cubic G A) -> (x * y) * z ≡ x * (y * z)
  *-assoc-Cub x y z = begin
    (x * y) * z                                           ≡⟨ cong (λ w -> (w * y) * z) (split x) ⟩
    ((x₀ + (x₁ + x₂)) * y) * z                            ≡⟨ cong (_* z) (distrib₃ x₀ x₁ x₂ y) ⟩
    (x₀ * y + (x₁ * y + x₂ * y)) * z                      ≡⟨ distrib₃ (x₀ * y) (x₁ * y) (x₂ * y) z ⟩
    (x₀ * y) * z + ((x₁ * y) * z + (x₂ * y) * z)          ≡⟨ cong₂ _+_ (assoc₀ x y z) (cong₂ _+_ (assoc₁ x y z) (assoc₂ x y z)) ⟩
    x₀ * (y * z) + (x₁ * (y * z) + x₂ * (y * z))          ≡⟨ sym (distrib₃ x₀ x₁ x₂ (y * z)) ⟩
    (x₀ + (x₁ + x₂)) * (y * z)                            ≡⟨ cong (_* (y * z)) (sym (split x)) ⟩
    x * (y * z)                                           ∎
    where
      open ≡-Reasoning
      x₀ x₁ x₂ : Cubic G A
      x₀ = part₀ x
      x₁ = part₁ x
      x₂ = part₂ x

  isCommutativeRing-Cub : IsCommutativeRing _≡_ _+_ _*_ -_ 0# (1# {Cubic G A})
  isCommutativeRing-Cub = isCommutativeRing-from-laws _ _ _ _ _ record
    { +-assoc = +-assoc-Cub
    ; +-comm = +-comm-Cub
    ; +-identityˡ = +-identityˡ-Cub
    ; -‿inverseˡ = -‿inverseˡ-Cub
    ; *-assoc = *-assoc-Cub
    ; *-comm = *-comm-Cub
    ; *-identityˡ = *-identityˡ-Cub
    ; distribʳ = distribʳ-Cub
    }

  commutativeRing-Cub : CommutativeRing 0ℓ 0ℓ
  commutativeRing-Cub = record { isCommutativeRing = isCommutativeRing-Cub }

  -- The constant-coefficient embedding A → A[θ] is a ring homomorphism.
  lift-Cub-isRingHom : Hom.IsRingHom (lift-Cub {G} {A})
  lift-Cub-isRingHom = record
    { multiplicative = record
      { f-* = λ a b -> by (env a b) (Cub (v₀ * v₁) 0# 0#) (Cub v₀ 0# 0# * Cub v₁ 0# 0#) refl refl refl
      ; f-1 = refl }
    ; f-+ = λ a b -> by (env a b) (Cub (v₀ + v₁) 0# 0#) (Cub v₀ 0# 0# + Cub v₁ 0# 0#) refl refl refl
    ; f-0 = refl
    ; f-neg = λ a -> by (env a a) (Cub (- v₀) 0# 0#) (- Cub v₀ 0# 0#) refl refl refl }
    where
      env : A -> A -> Vec A 10
      env a b = a ∷ b ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ cubic-s {G} ∷ []
