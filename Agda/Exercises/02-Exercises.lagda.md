# Week 02 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 02-Exercises where

open import prelude
open import decidability
open import sums
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry ABX (a , b) = ABX a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry ABX a b = ABX (a , b)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?


### Exercise 2 (★)

Consider the following goals:
```agda
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = inl a , inl b
[i] (inr c) = inr c , inr c

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl a , c) = inl (a , c)
[ii] (inr b , c) = inr (b , c)

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] ¬AB = (λ ¬A → ¬AB (inl ¬A)) , (λ ¬B → ¬AB (inr ¬B)) 

postulate
  [iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
--[iv] h = {! !}
--to provide constructive proof we need to determine which constructor of disjunction choose but it is not posible to deduce from ¬ (A × B)
--also it is possible to prove that this is equivalent to LEM

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] AB ¬B a = ¬B (AB a)

postulate
  [vi] : {A B : Type} → (¬ A → ¬ B) → B → A
--[vi] ¬A→¬B b = {! !}
--we need to construct A which is not possible if there is no function which return A or if we do not know its constructors. only way is to construct 𝟘 type. this is possible if we can get B and ¬B, to get ¬B we need to get ¬A which is imposible in corrent context 
--we can prove that it is equivalent to LEM
lem-eqv : ((A B : Type) → (¬ A → ¬ B) → B → A) → ((P : Type) → P ∔ (¬ P))
lem-eqv h P = h _ 𝟙 (λ lem _ → lem (inr λ p → lem (inl p))) ⋆ 
--it is trivial to other side of equivalence 

postulate
  [vii] : {A B : Type} → ((A → B) → A) → A
--[vii] ABA = ABA λ a → {!   !} 
--we can not prove because of almost same reasons as above one
--we can prove that it is equivalent to LEM

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a

[viii] ¬Σ a Ba = ¬Σ (a , Ba) 

postulate
  [ix] : {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
--[ix] ¬∀ = {!   !} , {!   !}
--to prove sum type we need to provide withness of A which is not possible to construct from negation

[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] aΣCab = (λ a → aΣCab a .pr₁) , λ a → aΣCab a .pr₂ 
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne ¬¬¬A a = ¬¬¬A (λ ¬A → ¬A a)
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor AB ¬¬A ¬B = ¬¬A (λ a → ¬B (AB a))

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli A¬¬B ¬¬A ¬B = ¬¬A λ a → A¬¬B a ¬B
```
Hint: For the second goal use `tne` from the previous exercise





## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true = 𝟘
bool-as-type false = 𝟙
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)


### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ true true eq = (λ ()) , (λ ())
bool-≡-char₁ false false eq = id , id
```


### Exercise 3 (★★)

Using ex. 2, conclude that
```agda
true≢false : ¬ (true ≡ false)
true≢false ()
```
You can actually prove this much easier! How?


### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true eqv = refl _
bool-≡-char₂ true false (pr₃ , pr₄ ) = 𝟘-elim (pr₄ ⋆)
bool-≡-char₂ false true (pr₃ , pr₄) = 𝟘-elim (pr₃ ⋆)
bool-≡-char₂ false false eqv = refl _
```


## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```

Prove that

```agda
decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
decidable-equality-char A = (λ hd → equality-dec hd , decidable-equality-char→ hd) ,  
                            decidable-equality-char← 
  where 
    equality-dec : has-decidable-equality A → A → A → Bool
    equality-dec hd a₁ a₂ with hd a₁ a₂ 
    ... | inl a₁eqa₂ = true
    ... | inr a₁neqa₂ = false

    decidable-equality-char→ : (hd : has-decidable-equality A) → (a₁ : A) → (a₂ : A) → a₁ ≡ a₂ ⇔ equality-dec hd a₁ a₂ ≡ true
    decidable-equality-char→ hd a₁ a₂ with hd a₁ a₂
    ... | inl a₁≡a₂ = (λ _ → refl _) , λ _ → a₁≡a₂
    ... | inr a₁≠a₂ = (λ a₁≡a₂ → 𝟘-nondep-elim (a₁≠a₂ a₁≡a₂)) , λ ()

    fneqt : (false ≡ true) → 𝟘
    fneqt ()

    decidable-equality-char← : has-bool-dec-fct A → has-decidable-equality A
    decidable-equality-char← (hb , pr₄) a₁ a₂ with hb a₁ a₂ | pr₄ a₁ a₂ 
    ... | true | pr₃ , pr₅ = inl (pr₅ (refl true))
    ... | false | pr₃ , pr₅ = inr (λ{ a₁≡a₂ → fneqt (pr₃ a₁≡a₂) })

```
  