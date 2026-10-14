-- The rings ℤ[1/ p ] of Quantum.Synthesis.Ring.Localized are
-- commutative rings, for every p ≥ 2.
--
-- The proof is the one for the dyadic fractions (Properties.Dyadic):
-- the map toℚ : ℤ[1/ p ] → ℚ is an injective ring homomorphism
-- (injective, since the representation is canonical; this needs only
-- p ≥ 2, not that p is prime), so the ring laws transfer from ℚ. To
-- compute with the smart constructor "frac a n" = a/pⁿ, we go through
-- the unnormalised rationals ℚᵘ, where a/pⁿ is the pair (a, pⁿ).

{-# OPTIONS --without-K --safe #-}

module Quantum.Synthesis.Ring.Properties.Localized where

open import Level using (0ℓ)
open import Algebra.Bundles using (CommutativeRing ; RawRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Algebra.Morphism.Structures using (IsRingMonomorphism)
import Algebra.Morphism.RingMonomorphism as RingMonomorphisms
open import Data.Bool.Base using (Bool ; true ; false ; T ; not)
open import Data.Empty using (⊥-elim ; ⊥-elim-irr)
open import Data.Unit.Base using (tt)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
import Data.Nat.DivMod as ℕDM
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
import Data.Integer.DivMod as IDM
import Data.Integer.Solver as ℤSolver
open import Data.Rational.Base as ℚ using (ℚ)
import Data.Rational.Properties as ℚP
import Data.Rational.Unnormalised.Base as ℚᵘ
open import Data.Rational.Unnormalised.Base using (ℚᵘ ; *≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; module ≡-Reasoning)
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable.Core using (T?)

open import Instances hiding (_≟_ ; _/_ ; _%_ ; _≤_ ; _<_)
open import Quantum.Synthesis.Ring.Localized
  using (ℤ[1/_] ; Frac' ; frac ; divides ; CanonicalFrac ; SemiRingFrac ; RingFrac ; ToRationalFrac)

open ℤSolver.+-*-Solver using (solve ; _:=_ ; _:+_ ; _:*_ ; con)

-- ----------------------------------------------------------------------
-- * Generic lemmas on ℚᵘ (as in Properties.Dyadic)

private
  recompute-T : ∀ b -> .(T b) -> T b
  recompute-T true _ = tt
  recompute-T false p = ⊥-elim-irr p

  T⇒≡true : ∀ {b} -> T b -> b ≡ true
  T⇒≡true {true} _ = refl

  /ᵘ-≃ : ∀ a b d e .{{_ : ℕ.NonZero d}} .{{_ : ℕ.NonZero e}} ->
         a ℤ.* + e ≡ b ℤ.* + d -> (a ℚᵘ./ d) ℚᵘ.≃ (b ℚᵘ./ e)
  /ᵘ-≃ a b (suc d) (suc e) eq = *≡* eq

  /ᵘ-≃⁻¹ : ∀ a b d e .{{_ : ℕ.NonZero d}} .{{_ : ℕ.NonZero e}} ->
           (a ℚᵘ./ d) ℚᵘ.≃ (b ℚᵘ./ e) -> a ℤ.* + e ≡ b ℤ.* + d
  /ᵘ-≃⁻¹ a b (suc d) (suc e) (*≡* eq) = eq

  /ᵘ-+ : ∀ a b d e .{{_ : ℕ.NonZero d}} .{{_ : ℕ.NonZero e}} ->
         (a ℚᵘ./ d) ℚᵘ.+ (b ℚᵘ./ e) ≡ ((a ℤ.* + e ℤ.+ b ℤ.* + d) ℚᵘ./ (d ℕ.* e)) {{ℕP.m*n≢0 d e}}
  /ᵘ-+ a b (suc d) (suc e) = refl

  /ᵘ-* : ∀ a b d e .{{_ : ℕ.NonZero d}} .{{_ : ℕ.NonZero e}} ->
         (a ℚᵘ./ d) ℚᵘ.* (b ℚᵘ./ e) ≡ ((a ℤ.* b) ℚᵘ./ (d ℕ.* e)) {{ℕP.m*n≢0 d e}}
  /ᵘ-* a b (suc d) (suc e) = refl

  /ᵘ-neg : ∀ a d .{{_ : ℕ.NonZero d}} -> ℚᵘ.- (a ℚᵘ./ d) ≡ (ℤ.- a) ℚᵘ./ d
  /ᵘ-neg a (suc d) = refl

  fromℚᵘ-/ : ∀ a d .{{_ : ℕ.NonZero d}} -> ℚ.fromℚᵘ (a ℚᵘ./ d) ≡ a ℚ./ d
  fromℚᵘ-/ a (suc d) = refl

  fromℚᵘ-+ : ∀ p q -> ℚ.fromℚᵘ (p ℚᵘ.+ q) ≡ ℚ.fromℚᵘ p ℚ.+ ℚ.fromℚᵘ q
  fromℚᵘ-+ p q = ℚP.toℚᵘ-injective (ℚᵘP.≃-trans (ℚP.toℚᵘ-fromℚᵘ (p ℚᵘ.+ q))
    (ℚᵘP.≃-trans (ℚᵘP.+-cong (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ p)) (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ q)))
      (ℚᵘP.≃-sym (ℚP.toℚᵘ-homo-+ (ℚ.fromℚᵘ p) (ℚ.fromℚᵘ q)))))

  fromℚᵘ-* : ∀ p q -> ℚ.fromℚᵘ (p ℚᵘ.* q) ≡ ℚ.fromℚᵘ p ℚ.* ℚ.fromℚᵘ q
  fromℚᵘ-* p q = ℚP.toℚᵘ-injective (ℚᵘP.≃-trans (ℚP.toℚᵘ-fromℚᵘ (p ℚᵘ.* q))
    (ℚᵘP.≃-trans (ℚᵘP.*-cong (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ p)) (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ q)))
      (ℚᵘP.≃-sym (ℚP.toℚᵘ-homo-* (ℚ.fromℚᵘ p) (ℚ.fromℚᵘ q)))))

  fromℚᵘ-neg : ∀ p -> ℚ.fromℚᵘ (ℚᵘ.- p) ≡ ℚ.- ℚ.fromℚᵘ p
  fromℚᵘ-neg p = ℚP.toℚᵘ-injective (ℚᵘP.≃-trans (ℚP.toℚᵘ-fromℚᵘ (ℚᵘ.- p))
    (ℚᵘP.≃-trans (ℚᵘP.-‿cong (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ p)))
      (ℚᵘP.≃-sym (ℚP.toℚᵘ-homo‿- (ℚ.fromℚᵘ p)))))

  +-lemma : ∀ a b (P J M : ℕ) -> M ≡ P ℕ.* J ->
            (a ℤ.* + J ℤ.+ b) ℤ.* + (P ℕ.* M) ≡ (a ℤ.* + M ℤ.+ b ℤ.* + P) ℤ.* + M
  +-lemma a b P J .(P ℕ.* J) refl = begin
    (a ℤ.* + J ℤ.+ b) ℤ.* + (P ℕ.* (P ℕ.* J))
      ≡⟨ cong (λ z -> (a ℤ.* + J ℤ.+ b) ℤ.* z) (trans (ℤP.pos-* P (P ℕ.* J)) (cong (+ P ℤ.*_) (ℤP.pos-* P J))) ⟩
    (a ℤ.* + J ℤ.+ b) ℤ.* (+ P ℤ.* (+ P ℤ.* + J))
      ≡⟨ solve 4 (λ a b p j -> (a :* j :+ b) :* (p :* (p :* j)) := (a :* (p :* j) :+ b :* p) :* (p :* j))
           refl a b (+ P) (+ J) ⟩
    (a ℤ.* (+ P ℤ.* + J) ℤ.+ b ℤ.* + P) ℤ.* (+ P ℤ.* + J)
      ≡⟨ cong₂ (λ z w -> (a ℤ.* z ℤ.+ b ℤ.* + P) ℤ.* w) (sym (ℤP.pos-* P J)) (sym (ℤP.pos-* P J)) ⟩
    (a ℤ.* + (P ℕ.* J) ℤ.+ b ℤ.* + P) ℤ.* + (P ℕ.* J) ∎
    where open ≡-Reasoning

  +-lemma' : ∀ a b (P J N : ℕ) -> N ≡ P ℕ.* J ->
             (a ℤ.+ b ℤ.* + J) ℤ.* + (N ℕ.* P) ≡ (a ℤ.* + P ℤ.+ b ℤ.* + N) ℤ.* + N
  +-lemma' a b P J .(P ℕ.* J) refl = begin
    (a ℤ.+ b ℤ.* + J) ℤ.* + ((P ℕ.* J) ℕ.* P)
      ≡⟨ cong (λ z -> (a ℤ.+ b ℤ.* + J) ℤ.* z) (trans (ℤP.pos-* (P ℕ.* J) P) (cong (ℤ._* + P) (ℤP.pos-* P J))) ⟩
    (a ℤ.+ b ℤ.* + J) ℤ.* ((+ P ℤ.* + J) ℤ.* + P)
      ≡⟨ solve 4 (λ a b p j -> (a :+ b :* j) :* ((p :* j) :* p) := (a :* p :+ b :* (p :* j)) :* (p :* j))
           refl a b (+ P) (+ J) ⟩
    (a ℤ.* + P ℤ.+ b ℤ.* (+ P ℤ.* + J)) ℤ.* (+ P ℤ.* + J)
      ≡⟨ cong₂ (λ z w -> (a ℤ.* + P ℤ.+ b ℤ.* z) ℤ.* w) (sym (ℤP.pos-* P J)) (sym (ℤP.pos-* P J)) ⟩
    (a ℤ.* + P ℤ.+ b ℤ.* + (P ℕ.* J)) ℤ.* + (P ℕ.* J) ∎
    where open ≡-Reasoning

-- ----------------------------------------------------------------------
-- * ℤ[1/ p ] for p = q + 2

module _ (q : ℕ) where

  private
    p : ℕ
    p = suc (suc q)

    -- pⁿ (this is the p^ of Quantum.Synthesis.Ring.Localized).
    P^ : ℕ -> ℕ
    P^ n = p ℕ.^ n

    nz : ∀ n -> ℕ.NonZero (P^ n)
    nz n = ℕP.m^n≢0 p n

    P^-split : ∀ n m -> n ℕ.≤ m -> P^ m ≡ P^ n ℕ.* P^ (m ℕ.∸ n)
    P^-split n m n≤m = trans (cong P^ (sym (ℕP.m+[n∸m]≡n n≤m))) (ℕP.^-distribˡ-+-* p n (m ℕ.∸ n))

    -- If p ∣ a, then a = (a/p)·p.
    divides⇒%ℕ≡0 : ∀ a -> divides p a ≡ true -> a ℤ.%ℕ p ≡ 0
    divides⇒%ℕ≡0 (+ n) eq = ℕP.≡ᵇ⇒≡ (n ℕ.% p) 0 (subst T (sym eq) tt)
    divides⇒%ℕ≡0 -[1+ n ] eq with suc n ℕ.% p | ℕP.≡ᵇ⇒≡ (suc n ℕ.% p) 0 (subst T (sym eq) tt)
    ... | zero | _ = refl
    ... | suc _ | ()

    div-exact : ∀ a -> divides p a ≡ true -> (a ℤ./ℕ p) ℤ.* + p ≡ a
    div-exact a eq = sym (begin
      a                                     ≡⟨ IDM.a≡a%ℕn+[a/ℕn]*n a p ⟩
      + (a ℤ.%ℕ p) ℤ.+ (a ℤ./ℕ p) ℤ.* + p   ≡⟨ cong (λ r -> + r ℤ.+ (a ℤ./ℕ p) ℤ.* + p) (divides⇒%ℕ≡0 a eq) ⟩
      + 0 ℤ.+ (a ℤ./ℕ p) ℤ.* + p            ≡⟨ ℤP.+-identityˡ _ ⟩
      (a ℤ./ℕ p) ℤ.* + p                    ∎)
      where open ≡-Reasoning

    -- p ∣ a·(p·k).
    divides-* : ∀ a k -> divides p (a ℤ.* + (p ℕ.* k)) ≡ true
    divides-* a k = begin
      (ℤ.∣ a ℤ.* + (p ℕ.* k) ∣ ℕ.% p) ℕ.≡ᵇ 0   ≡⟨ cong (λ z -> (z ℕ.% p) ℕ.≡ᵇ 0) (ℤP.abs-* a (+ (p ℕ.* k))) ⟩
      ((ℤ.∣ a ∣ ℕ.* (p ℕ.* k)) ℕ.% p) ℕ.≡ᵇ 0    ≡⟨ cong (λ z -> (z ℕ.% p) ℕ.≡ᵇ 0) (lemma ℤ.∣ a ∣) ⟩
      (((ℤ.∣ a ∣ ℕ.* k) ℕ.* p) ℕ.% p) ℕ.≡ᵇ 0    ≡⟨ cong (ℕ._≡ᵇ 0) (ℕDM.m*n%n≡0 (ℤ.∣ a ∣ ℕ.* k) p) ⟩
      true                                      ∎
      where
        open ≡-Reasoning
        lemma : ∀ m -> m ℕ.* (p ℕ.* k) ≡ (m ℕ.* k) ℕ.* p
        lemma m = trans (cong (m ℕ.*_) (ℕP.*-comm p k)) (sym (ℕP.*-assoc m k p))

    -- a·p^(n+1+j) = b·pⁿ implies that p ∣ b.
    divides-lemma : ∀ a b n j -> a ℤ.* + P^ (suc (n ℕ.+ j)) ≡ b ℤ.* + P^ n -> divides p b ≡ true
    divides-lemma a b n j eq = trans (cong (divides p) (sym b≡)) (divides-* a (P^ j))
      where
        N J : ℕ
        N = P^ n
        J = P^ j
        open ≡-Reasoning
        lemma : a ℤ.* + (p ℕ.* (N ℕ.* J)) ≡ (a ℤ.* + (p ℕ.* J)) ℤ.* + N
        lemma = begin
          a ℤ.* + (p ℕ.* (N ℕ.* J))            ≡⟨ cong (a ℤ.*_) (ℤP.pos-* p (N ℕ.* J)) ⟩
          a ℤ.* (+ p ℤ.* + (N ℕ.* J))          ≡⟨ cong (λ z -> a ℤ.* (+ p ℤ.* z)) (ℤP.pos-* N J) ⟩
          a ℤ.* (+ p ℤ.* (+ N ℤ.* + J))        ≡⟨ solve 4 (λ a t n j -> a :* (t :* (n :* j)) := (a :* (t :* j)) :* n)
                                                     refl a (+ p) (+ N) (+ J) ⟩
          (a ℤ.* (+ p ℤ.* + J)) ℤ.* + N        ≡⟨ cong (λ z -> (a ℤ.* z) ℤ.* + N) (sym (ℤP.pos-* p J)) ⟩
          (a ℤ.* + (p ℕ.* J)) ℤ.* + N          ∎
        b≡ : a ℤ.* + (p ℕ.* J) ≡ b
        b≡ = ℤP.*-cancelʳ-≡ _ _ (+ N) {{nz n}} (begin
          (a ℤ.* + (p ℕ.* J)) ℤ.* + N           ≡⟨ sym lemma ⟩
          a ℤ.* + (p ℕ.* (N ℕ.* J))             ≡⟨ cong (λ k -> a ℤ.* + (p ℕ.* k)) (sym (ℕP.^-distribˡ-+-* p n j)) ⟩
          a ℤ.* + P^ (suc (n ℕ.+ j))            ≡⟨ eq ⟩
          b ℤ.* + N                             ∎)

  -- --------------------------------------------------------------------
  -- ** Fractions as unnormalised rationals

  private
    infix 8 _/p^_
    _/p^_ : ℤ -> ℕ -> ℚᵘ
    a /p^ n = (a ℚᵘ./ P^ n) {{nz n}}

    u : ℤ[1/ p ] -> ℚᵘ
    u (Frac' a n _) = a /p^ n

    toℚ-u : ∀ x -> toℚ x ≡ ℚ.fromℚᵘ (u x)
    toℚ-u (Frac' a n _) = sym (fromℚᵘ-/ a (P^ n) {{nz n}})

    Frac'-cong : ∀ {a b n m} .{c c'} -> a ≡ b -> n ≡ m -> Frac' {p} a n c ≡ Frac' b m c'
    Frac'-cong refl refl = refl

    -- Canonical representations of the same number are equal.
    canonical-unique : ∀ a n b m -> T (CanonicalFrac p a n) -> T (CanonicalFrac p b m) ->
                       a ℤ.* + P^ m ≡ b ℤ.* + P^ n -> (a ≡ b) × (n ≡ m)
    canonical-unique a n b m ca cb eq with ℕP.<-cmp n m
    ... | tri≈ _ refl _ = ℤP.*-cancelʳ-≡ a b (+ P^ n) {{nz n}} eq , refl
    ... | tri< n<m _ _ = ⊥-elim (subst (λ t -> T (not t)) (divides-lemma a b n j eq') cb')
      where
        j = m ℕ.∸ suc n
        hm : suc (n ℕ.+ j) ≡ m
        hm = ℕP.m+[n∸m]≡n n<m
        eq' : a ℤ.* + P^ (suc (n ℕ.+ j)) ≡ b ℤ.* + P^ n
        eq' = subst (λ k -> a ℤ.* + P^ k ≡ b ℤ.* + P^ n) (sym hm) eq
        cb' : T (CanonicalFrac p b (suc (n ℕ.+ j)))
        cb' = subst (λ k -> T (CanonicalFrac p b k)) (sym hm) cb
    ... | tri> _ _ m<n = ⊥-elim (subst (λ t -> T (not t)) (divides-lemma b a m j eq') ca')
      where
        j = n ℕ.∸ suc m
        hn : suc (m ℕ.+ j) ≡ n
        hn = ℕP.m+[n∸m]≡n m<n
        eq' : b ℤ.* + P^ (suc (m ℕ.+ j)) ≡ a ℤ.* + P^ m
        eq' = subst (λ k -> b ℤ.* + P^ k ≡ a ℤ.* + P^ m) (sym hn) (sym eq)
        ca' : T (CanonicalFrac p a (suc (m ℕ.+ j)))
        ca' = subst (λ k -> T (CanonicalFrac p a k)) (sym hn) ca

  toℚ-injective-Frac : ∀ {x y : ℤ[1/ p ]} -> toℚ x ≡ toℚ y -> x ≡ y
  toℚ-injective-Frac {x@(Frac' a n c)} {y@(Frac' b m c')} eq
    with canonical-unique a n b m (recompute-T _ c) (recompute-T _ c')
           (/ᵘ-≃⁻¹ a b (P^ n) (P^ m) {{nz n}} {{nz m}}
             (ℚP.fromℚᵘ-injective (trans (sym (toℚ-u x)) (trans eq (toℚ-u y)))))
  ... | a≡b , n≡m = Frac'-cong a≡b n≡m

  -- --------------------------------------------------------------------
  -- ** The smart constructor

  private
    -- Dividing out p: (a/p)/pⁿ = a/pⁿ⁺¹.
    divp-≃ : ∀ a n -> T (divides p a) -> (a ℤ./ℕ p) /p^ n ℚᵘ.≃ a /p^ (suc n)
    divp-≃ a n d = /ᵘ-≃ (a ℤ./ℕ p) a (P^ n) (P^ (suc n)) {{nz n}} {{nz (suc n)}} lemma
      where
        open ≡-Reasoning
        lemma : (a ℤ./ℕ p) ℤ.* + P^ (suc n) ≡ a ℤ.* + P^ n
        lemma = begin
          (a ℤ./ℕ p) ℤ.* + (p ℕ.* P^ n)         ≡⟨ cong ((a ℤ./ℕ p) ℤ.*_) (ℤP.pos-* p (P^ n)) ⟩
          (a ℤ./ℕ p) ℤ.* (+ p ℤ.* + P^ n)       ≡⟨ sym (ℤP.*-assoc (a ℤ./ℕ p) (+ p) (+ P^ n)) ⟩
          ((a ℤ./ℕ p) ℤ.* + p) ℤ.* + P^ n       ≡⟨ cong (ℤ._* + P^ n) (div-exact a (T⇒≡true d)) ⟩
          a ℤ.* + P^ n                          ∎

  -- (frac first distinguishes the numerator 0, so the cases a = + suc _
  -- and a = -[1+ _ ] are treated separately.)
  u-frac : ∀ a n -> u (frac a n) ℚᵘ.≃ a /p^ n
  u-frac (+ zero) n = /ᵘ-≃ (+ zero) (+ zero) 1 (P^ n) {{_}} {{nz n}} refl
  u-frac a@(+ suc _) zero = ℚᵘP.≃-refl
  u-frac a@(-[1+ _ ]) zero = ℚᵘP.≃-refl
  u-frac a@(+ suc _) (suc n) with T? (divides p a)
  ... | yes d = ℚᵘP.≃-trans (u-frac (a ℤ./ℕ p) n) (divp-≃ a n d)
  ... | no _ = ℚᵘP.≃-refl
  u-frac a@(-[1+ _ ]) (suc n) with T? (divides p a)
  ... | yes d = ℚᵘP.≃-trans (u-frac (a ℤ./ℕ p) n) (divp-≃ a n d)
  ... | no _ = ℚᵘP.≃-refl

  frac-spec : ∀ a n -> toℚ (frac {p} a n) ≡ (a ℚ./ P^ n) {{nz n}}
  frac-spec a n = trans (toℚ-u (frac a n)) (trans (ℚP.fromℚᵘ-cong (u-frac a n)) (fromℚᵘ-/ a (P^ n) {{nz n}}))

  -- --------------------------------------------------------------------
  -- ** toℚ is a ring homomorphism

  private
    u-+ : ∀ x y -> u (x + y) ℚᵘ.≃ u x ℚᵘ.+ u y
    u-+ (Frac' a n _) (Frac' b m _) with n ℕ.≤ᵇ m in le
    ... | true = ℚᵘP.≃-trans (u-frac (a ℤ.* + P^ (m ℕ.∸ n) ℤ.+ b) m)
                   (ℚᵘP.≃-trans (/ᵘ-≃ _ _ (P^ m) (P^ n ℕ.* P^ m) {{nz m}} {{ℕP.m*n≢0 _ _ {{nz n}} {{nz m}}}}
                                   (+-lemma a b (P^ n) (P^ (m ℕ.∸ n)) (P^ m) (P^-split n m n≤m)))
                     (ℚᵘP.≃-reflexive (sym (/ᵘ-+ a b (P^ n) (P^ m) {{nz n}} {{nz m}}))))
      where
        n≤m : n ℕ.≤ m
        n≤m = ℕP.≤ᵇ⇒≤ n m (subst T (sym le) tt)
    ... | false = ℚᵘP.≃-trans (u-frac (a ℤ.+ b ℤ.* + P^ (n ℕ.∸ m)) n)
                   (ℚᵘP.≃-trans (/ᵘ-≃ _ _ (P^ n) (P^ n ℕ.* P^ m) {{nz n}} {{ℕP.m*n≢0 _ _ {{nz n}} {{nz m}}}}
                                   (+-lemma' a b (P^ m) (P^ (n ℕ.∸ m)) (P^ n) (P^-split m n m≤n)))
                     (ℚᵘP.≃-reflexive (sym (/ᵘ-+ a b (P^ n) (P^ m) {{nz n}} {{nz m}}))))
      where
        m≤n : m ℕ.≤ n
        m≤n = ℕP.≰⇒≥ (λ n≤m -> subst T le (ℕP.≤⇒≤ᵇ n≤m))

    u-* : ∀ x y -> u (x * y) ℚᵘ.≃ u x ℚᵘ.* u y
    u-* (Frac' a n _) (Frac' b m _) =
      ℚᵘP.≃-trans (u-frac (a ℤ.* b) (n ℕ.+ m))
        (ℚᵘP.≃-trans (/ᵘ-≃ _ _ (P^ (n ℕ.+ m)) (P^ n ℕ.* P^ m) {{nz (n ℕ.+ m)}} {{ℕP.m*n≢0 _ _ {{nz n}} {{nz m}}}}
                        (cong (λ k -> (a ℤ.* b) ℤ.* + k) (sym (ℕP.^-distribˡ-+-* p n m))))
          (ℚᵘP.≃-reflexive (sym (/ᵘ-* a b (P^ n) (P^ m) {{nz n}} {{nz m}}))))

    u-neg : ∀ x -> u (- x) ℚᵘ.≃ ℚᵘ.- u x
    u-neg (Frac' a n _) = ℚᵘP.≃-trans (u-frac (ℤ.- a) n) (ℚᵘP.≃-reflexive (sym (/ᵘ-neg a (P^ n) {{nz n}})))

  toℚ-+-Frac : ∀ (x y : ℤ[1/ p ]) -> toℚ (x + y) ≡ toℚ x ℚ.+ toℚ y
  toℚ-+-Frac x y = begin
    toℚ (x + y)                         ≡⟨ toℚ-u (x + y) ⟩
    ℚ.fromℚᵘ (u (x + y))                ≡⟨ ℚP.fromℚᵘ-cong (u-+ x y) ⟩
    ℚ.fromℚᵘ (u x ℚᵘ.+ u y)             ≡⟨ fromℚᵘ-+ (u x) (u y) ⟩
    ℚ.fromℚᵘ (u x) ℚ.+ ℚ.fromℚᵘ (u y)   ≡⟨ sym (cong₂ ℚ._+_ (toℚ-u x) (toℚ-u y)) ⟩
    toℚ x ℚ.+ toℚ y                     ∎
    where open ≡-Reasoning

  toℚ-*-Frac : ∀ (x y : ℤ[1/ p ]) -> toℚ (x * y) ≡ toℚ x ℚ.* toℚ y
  toℚ-*-Frac x y = begin
    toℚ (x * y)                         ≡⟨ toℚ-u (x * y) ⟩
    ℚ.fromℚᵘ (u (x * y))                ≡⟨ ℚP.fromℚᵘ-cong (u-* x y) ⟩
    ℚ.fromℚᵘ (u x ℚᵘ.* u y)             ≡⟨ fromℚᵘ-* (u x) (u y) ⟩
    ℚ.fromℚᵘ (u x) ℚ.* ℚ.fromℚᵘ (u y)   ≡⟨ sym (cong₂ ℚ._*_ (toℚ-u x) (toℚ-u y)) ⟩
    toℚ x ℚ.* toℚ y                     ∎
    where open ≡-Reasoning

  toℚ-neg-Frac : ∀ (x : ℤ[1/ p ]) -> toℚ (- x) ≡ ℚ.- toℚ x
  toℚ-neg-Frac x = begin
    toℚ (- x)                  ≡⟨ toℚ-u (- x) ⟩
    ℚ.fromℚᵘ (u (- x))         ≡⟨ ℚP.fromℚᵘ-cong (u-neg x) ⟩
    ℚ.fromℚᵘ (ℚᵘ.- u x)        ≡⟨ fromℚᵘ-neg (u x) ⟩
    ℚ.- ℚ.fromℚᵘ (u x)         ≡⟨ sym (cong ℚ.-_ (toℚ-u x)) ⟩
    ℚ.- toℚ x                  ∎
    where open ≡-Reasoning

  -- --------------------------------------------------------------------
  -- ** The commutative ring ℤ[1/ p ]

  rawRing-Frac : RawRing 0ℓ 0ℓ
  rawRing-Frac = record
    { Carrier = ℤ[1/ p ] ; _≈_ = _≡_ ; _+_ = _+_ ; _*_ = _*_ ; -_ = -_ ; 0# = 0# ; 1# = 1# }

  toℚ-isRingMonomorphism-Frac : IsRingMonomorphism rawRing-Frac ℚ.+-*-rawRing toℚ
  toℚ-isRingMonomorphism-Frac = record
    { isRingHomomorphism = record
      { isSemiringHomomorphism = record
        { isNearSemiringHomomorphism = record
          { +-isMonoidHomomorphism = record
            { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = cong toℚ }
              ; homo = toℚ-+-Frac }
            ; ε-homo = refl }
          ; *-homo = toℚ-*-Frac }
        ; 1#-homo = refl }
      ; -‿homo = toℚ-neg-Frac }
    ; injective = toℚ-injective-Frac }

  isCommutativeRing-Frac : IsCommutativeRing (_≡_ {A = ℤ[1/ p ]}) _+_ _*_ -_ 0# 1#
  isCommutativeRing-Frac =
    RingMonomorphisms.isCommutativeRing toℚ-isRingMonomorphism-Frac ℚP.+-*-isCommutativeRing

  commutativeRing-Frac : CommutativeRing 0ℓ 0ℓ
  commutativeRing-Frac = record { isCommutativeRing = isCommutativeRing-Frac }
