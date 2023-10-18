module Ternary.Properties where

open import Ternary.Base
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_; id)
open import Data.Nat as ℕ using (ℕ)
open import Function.Definitions
import Data.Nat.Properties as ℕₚ

open import Algebra.Definitions {A = ℕᵗ} _≡_

+-comm : Commutative _+_
+-comm zero zero = refl
+-comm zero 3[1+ y ] = refl
+-comm zero 1+[3 y ] = refl
+-comm zero 2+[3 y ] = refl
+-comm 3[1+ x ] zero = refl
+-comm 3[1+ x ] 3[1+ y ] = cong 3[1+_] (cong suc (+-comm x y))
+-comm 3[1+ x ] 1+[3 y ] = cong 1+[3_] (cong suc (+-comm x y))
+-comm 3[1+ x ] 2+[3 y ] = cong 2+[3_] (cong suc (+-comm x y))
+-comm 1+[3 x ] zero = refl
+-comm 1+[3 x ] 3[1+ y ] = cong 1+[3_] (cong suc (+-comm x y))
+-comm 1+[3 x ] 1+[3 y ] = cong 2+[3_] (+-comm x y)
+-comm 1+[3 x ] 2+[3 y ] = cong 3[1+_] (+-comm x y)
+-comm 2+[3 x ] zero = refl
+-comm 2+[3 x ] 3[1+ y ] = cong 2+[3_] (cong suc (+-comm x y))
+-comm 2+[3 x ] 1+[3 y ] = cong 3[1+_] (+-comm x y)
+-comm 2+[3 x ] 2+[3 y ] = cong 1+[3_] (cong suc (+-comm x y))

toℕ-suc : ∀ x → toℕ (suc x) ≡ ℕ.suc (toℕ x)
toℕ-suc zero = refl
toℕ-suc 3[1+ x ] = cong ℕ.suc (cong (3 ℕ.*_) (toℕ-suc x))
toℕ-suc 1+[3 x ] = refl
toℕ-suc 2+[3 x ] = ℕₚ.*-distribˡ-+ 3 1 (toℕ x)

toℕ-fromℕ : toℕ ∘ fromℕ ≗ id
toℕ-fromℕ ℕ.zero = refl
toℕ-fromℕ (ℕ.suc x) = trans (toℕ-suc (fromℕ x)) (cong ℕ.suc (toℕ-fromℕ x))

open ≡-Reasoning

toℕ-injective : Injective _≡_ _≡_ toℕ
toℕ-injective {zero} {zero} _ = refl
toℕ-injective {3[1+ x ]} {3[1+ y ]} eq = ?
toℕ-injective {3[1+ x ]} {1+[3 y ]} eq = ?
toℕ-injective {3[1+ x ]} {2+[3 y ]} eq = ?
toℕ-injective {1+[3 x ]} {y} eq = {!!}
toℕ-injective {2+[3 x ]} {y} eq = {!!}

fromℕ-toℕ : fromℕ ∘ toℕ ≗ id
fromℕ-toℕ zero = refl
fromℕ-toℕ 3[1+ x ] = begin
  fromℕ (toℕ 3[1+ x ]) ≡⟨⟩
  fromℕ (3 ℕ.* ℕ.suc (toℕ x)) ≡˘⟨ cong (λ ∙ → fromℕ (3 ℕ.* ∙)) (toℕ-suc x) ⟩
  fromℕ (3 ℕ.* toℕ (suc x)) ≡⟨ {! !} ⟩
  3[1+ x ] ∎
fromℕ-toℕ 1+[3 x ] = {!!}
fromℕ-toℕ 2+[3 x ] = {!!}
