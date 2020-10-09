module Data.Nat

import Syntax.PreorderReasoning

--nat_semigroup : Semigroup Nat
--nat_semigroup = Semigroup' Nat (+) plus_associativity

--data Nat = Z | S Nat
total
plus_left_identity : {n: Nat} -> 0 + n = n
plus_left_identity = Refl

total
plus_right_identity : {n: Nat} -> n + 0 = n
plus_right_identity {n = Z} = Refl
plus_right_identity {n = (S k)} = cong (plus_right_identity {n = k})

total
plus_successor : {n, m : Nat} -> n + (S m) = S (n + m)
plus_successor {n = Z} {m = m} = Refl
plus_successor {n = (S k)} {m = m} = cong plus_successor

total
transitivity : (a = b) -> (b = c) -> a = c
transitivity Refl Refl = Refl

total
plus_commutivity : {n, m : Nat} -> n + m = m + n
plus_commutivity {n = Z} {m = m} = sym (plus_right_identity {n = m})
plus_commutivity {n = (S k)} {m = m} =
  (S (k + m)) ={ cong {f = S} plus_commutivity }=
  (S (m + k)) ={ sym plus_successor }=
  (m + (S k)) QED

total
plus_associativity : {x, y, z : Nat} -> x + (y + z) = (x + y) + z
plus_associativity {x = Z} {y = y} {z = z} = Refl
plus_associativity {x = (S k)} {y = y} {z = z} = let rec = plus_associativity {x = k} {y} {z} in cong rec


total
mult_right_identity : {n : Nat} -> n * 1 = n
mult_right_identity {n = Z} = Refl
mult_right_identity {n = (S k)} = cong mult_right_identity

total
mult_left_identity : {n : Nat} -> n = n * 1
mult_left_identity = sym mult_right_identity

total
mult_right_zero : {m : Nat} -> m * 0 = 0
mult_right_zero {m = Z} = Refl
mult_right_zero {m = (S k)} = mult_right_zero {m = k}

total
mult_left_zero : {m : Nat} -> 0 * m = 0
mult_left_zero = Refl

total
lemma3 : {n : Nat} -> n * 1 = n + 0
lemma3 = transitivity mult_right_identity (sym plus_right_identity)

total
mult_succ : {m, n : Nat} -> m * (S n) = (m * n) + m
mult_succ {m = Z} {n = n} = Refl
mult_succ {m = (S k)} {n = n} =
  (S k * S n)           ={ Refl }=
  (S n + k * S n )      ={ Refl }=
  (S (n + k * S n))     ={ cong {f = S . (n +)} (mult_succ {m=k} {n}) }=
  (S (n + (k * n + k))) ={ cong {f = S} plus_commutivity }=
  (S ((k * n + k) + n)) ={ cong {f = S . (+ n)} plus_commutivity }=
  (S ((k + k * n) + n)) ={ Refl }=
  ((S k + k * n) + n)   ={ plus_commutivity }=
  (n + (S k + k * n))   ={ cong { f = (n +)} plus_commutivity }=
  (n + (k * n + S k))   ={ plus_associativity }=
  ((n + k * n) + S k)   ={ Refl }=
  (S k * n + S k)          QED

--lemma : {m, n : Nat} -> m + (m * n) = m * (S n)
--lemma {m} {n} = sym (mult_succ {m} {n})

total
distributivity : {a, b, c : Nat} -> a * (b + c) = (a * b) + (a * c)
distributivity {a} {b = Z} {c} = rewrite mult_right_zero {m = a} in Refl
distributivity {a} {b = (S k)} {c} =
  (a * (S (k + c)))     ={ mult_succ {m = a} {n = k + c} }=
  (a * (k + c) + a)     ={ cong {f = (+ a)} (distributivity {a} {b=k} {c}) }=
  ((a * k + a * c) + a) ={ sym plus_associativity }=
  (a * k + (a * c + a)) ={ cong {f = (plus (a * k))} (plus_commutivity {n=a * c} {m = a}) }= 
  (a * k + (a + a * c)) ={ plus_associativity }=
  ((a * k + a) + a * c) ={ cong {f = (+ a * c)} (sym mult_succ) }=
  ((a * S k) + (a * c))    QED

total
distributivity' : {a, b, c : Nat} -> a * (b + c) = (a * b) + (a * c)
distributivity'{a = Z} {b = b} {c = c} = Refl
distributivity'{a = (S k)} {b = b} {c = c} =
  (S k * (b + c))             ={ Refl }=
  ((b + c) + k * (b + c))     ={ cong {f = ((b + c) +)} (distributivity {a = k} {b} {c}) }=
  ((b + c) + (k * b + k * c)) ={ plus_associativity }=
  (((b + c) + k * b) + k * c) ={ cong {f = (+ k * c)} (sym plus_associativity) }=
  ((b + (c + k * b)) + k * c) ={ cong {f = ((+ k * c) . (b +))} plus_commutivity }=
  ((b + (k * b + c)) + k * c) ={ cong {f = (+ k * c)} plus_associativity }=
  (((b + k * b) + c) + k * c) ={ sym plus_associativity }=
  ((b + k * b) + (c + k * c)) ={ Refl }=
  ((S k * b) + (S k * c))            QED

total
mult_commutivity : {n, m : Nat} -> n * m = m * n
mult_commutivity {n = Z} {m = m} = sym mult_right_zero
mult_commutivity {n = (S k)} {m = m} =
  (S k * m)     ={ Refl }=
  (m + (k * m)) ={ plus_commutivity }=
  ((k * m) + m) ={ cong {f = (+ m)} (mult_commutivity {n = k} {m}) }=
  ((m * k) + m) ={ sym mult_succ }=
  (m * S k)        QED


data These a b = This' a | That' b | These' a b

total
non_zero_divisors : {m, n : Nat} -> m * n = 0 -> These (m = 0) (n = 0)
non_zero_divisors {m = Z} {n = Z} prf = These' Refl Refl
non_zero_divisors {m = Z} {n = (S k)} prf = This' Refl
non_zero_divisors {m = (S k)} {n = Z} prf = That' Refl
non_zero_divisors {m = (S _)} {n = (S _)} Refl impossible

-- Local Variables:
-- idris-load-packages: ("prelude" "contrib" "base")
-- End:
