module Ternary.Base where

open import Data.Nat as ℕ using (ℕ)
open import Function using (_∘_)

data ℕᵗ : Set where
  zero : ℕᵗ
  3[1+_] : ℕᵗ → ℕᵗ
  1+[3_] : ℕᵗ → ℕᵗ
  2+[3_] : ℕᵗ → ℕᵗ

suc : ℕᵗ → ℕᵗ
suc zero = 1+[3 zero ]
suc 3[1+ x ] = 1+[3 (suc x)]
suc 1+[3 x ] = 2+[3 x ]
suc 2+[3 x ] = 3[1+ x ]

triple : ℕᵗ → ℕᵗ
triple zero = zero
triple 3[1+ x ] = 3[1+ 2+[3 x ] ]
triple 1+[3 x ] = 3[1+ (triple x) ]
triple 2+[3 x ] = 3[1+ 1+[3 x ] ]

pred : ℕᵗ → ℕᵗ
pred zero = zero
pred 3[1+ x ] = 2+[3 x ]
pred 1+[3 x ] = triple x
pred 2+[3 x ] = 1+[3 x ]

infix 6 _+_

_+_ : ℕᵗ → ℕᵗ → ℕᵗ
zero + y = y
3[1+ x ] + zero = 3[1+ x ]
3[1+ x ] + 3[1+ y ] = 3[1+ suc (x + y)]
3[1+ x ] + 1+[3 y ] = suc 3[1+ (x + y)]
3[1+ x ] + 2+[3 y ] = suc (suc 3[1+ (x + y)])
1+[3 x ] + zero = 1+[3 x ]
1+[3 x ] + 3[1+ y ] = suc 3[1+ (x + y)]
1+[3 x ] + 1+[3 y ] = 2+[3 (x + y)]
1+[3 x ] + 2+[3 y ] = 3[1+ (x + y)]
2+[3 x ] + zero = 2+[3 x ]
2+[3 x ] + 3[1+ y ] = suc (suc 3[1+ (x + y)])
2+[3 x ] + 1+[3 y ] = 3[1+ (x + y)]
2+[3 x ] + 2+[3 y ] = suc 3[1+ (x + y)]

toℕ : ℕᵗ → ℕ
toℕ zero = 0
toℕ 3[1+ x ] = 3 ℕ.* (ℕ.suc (toℕ x))
toℕ 1+[3 x ] = ℕ.suc (3 ℕ.* toℕ x)
toℕ 2+[3 x ] = ℕ.suc (ℕ.suc (3 ℕ.* toℕ x))

fromℕ : ℕ → ℕᵗ
fromℕ ℕ.zero = zero
fromℕ (ℕ.suc x) = suc (fromℕ x)
