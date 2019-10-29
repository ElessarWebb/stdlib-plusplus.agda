module Data.List.All.Properties.Extra {a}{A : Set a} where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.List
open import Data.List.Any
open import Data.List.Membership.Propositional
open import Data.List.Properties.Extra
open import Data.List.At
open import Data.List.All as All
open import Data.List.All.Properties
open import Data.Product
open import Function

map-id′ : ∀ {p}{P : A → Set p}{l : List A} (ps : All P l) {f : ∀ {x : A} → P x → P x} →
         (∀ (x : A)(p : P x) → f {x} p ≡ p) →
         All.map f ps ≡ ps
map-id′ [] feq = refl
map-id′ (px ∷ ps) feq = cong₂ _∷_ (feq _ px) (map-id′ ps feq)

map-map : ∀ {p q r}{P : A → Set p}{Q : A → Set q}{R : A → Set r}{l : List A}(ps : All P l)
          {f : ∀ {x : A} → P x → Q x}{g : ∀ {x : A} → Q x → R x} →
          All.map g (All.map f ps) ≡ All.map (g ∘ f) ps
map-map [] = refl
map-map (px ∷ ps) = cong₂ _∷_ refl (map-map ps)

drop-all : ∀ {p}{P : A → Set p}{l : List A} n → All P l → All P (drop n l)
drop-all zero px = px
drop-all (suc n) [] = []
drop-all (suc n) (px ∷ pxs) = drop-all n pxs

split-++ : ∀ {p}{P : A → Set p}(l m : List A) → All P (l ++ m) → All P l × All P m
split-++ [] m pxs = [] , pxs
split-++ (x ∷ l) m (px ∷ pxs) with split-++ l m pxs
... | lp , rp = px ∷ lp , rp

_++-all_ : ∀ {l m p}{P : A → Set p} → All P l → All P m → All P (l ++ m)
[] ++-all pm = pm
(px ∷ pl) ++-all pm = px ∷ (pl ++-all pm)

∈-all : ∀ {p}{P : A → Set p}{l : List A}{x} → x ∈ l → All P l → P x
∈-all (here refl) (px ∷ q) = px
∈-all (there p) (px ∷ q) = ∈-all p q

_all-∷ʳ_ : ∀ {p}{l : List A} {x} {P : A → Set p} → All P l → P x → All P (l ∷ʳ x)
_all-∷ʳ_ [] q = q ∷ []
_all-∷ʳ_ (px ∷ p) q = px ∷ (p all-∷ʳ q)

all-∷ʳ∘map : ∀ {p q}{P : A → Set p}{Q : A → Set q}{xs : List A} {x}(pxs : All P xs)(px : P x)(f : ∀ {x} → P x → Q x) →
             (All.map f pxs) all-∷ʳ (f px) ≡ All.map f (pxs all-∷ʳ px)
all-∷ʳ∘map [] px f = refl
all-∷ʳ∘map (px₁ ∷ pxs) px f = cong₂ _∷_ refl (all-∷ʳ∘map pxs px f)

lookup∘map : ∀ {p q}{P : A → Set p}{Q : A → Set q}{xs : List A} {x}(pxs : All P xs)(e : x ∈ xs)(f : ∀ {x} → P x → Q x) →
             All.lookup (All.map f pxs) e ≡ f (All.lookup pxs e)
lookup∘map [] ()
lookup∘map (px ∷ pxs) (here refl) f = refl
lookup∘map (px ∷ pxs) (there e) f = lookup∘map pxs e f


erase : ∀ {p b}{P : A → Set p}{l : List A}{B : Set b} → (∀ {x} → P x → B) → All P l → List B
erase f [] = []
erase f (px ∷ xs₁) = f px ∷ erase f xs₁
