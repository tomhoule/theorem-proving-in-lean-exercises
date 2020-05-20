namespace chap8ex1

    open function

    #print surjective

    universes u v w
    variables {α : Type u} {β : Type v} {γ : Type w}
    open function

    lemma composition_check {g : β → γ} {f : α → β} : α → γ := g ∘ f

    lemma surjective_comp {g : β → γ} {f : α → β} (hg : surjective g) (hf : surjective f) :
    surjective (g ∘ f) :=
    λ lg,
    match (hg lg) with exists.intro (b: β) (beq : g b = lg) :=
        match (hf b) with exists.intro (a : α) (aeq : f a = b) :=
            begin
                existsi a,
                simp [aeq, beq]
            end
        end
    end

end chap8ex1

namespace chap8ex2

    namespace hidden

        open nat (zero succ)

        def addition : ℕ → ℕ → ℕ
        | m 0 := m
        | m (succ n) := succ (addition m n)

        lemma eight_plus_five_is_thirteen : addition 8 5 = 13 := rfl

        lemma zero_add : ∀ (n : ℕ), addition 0 n = n
        | 0 := by refl
        | (succ 0) := by refl
        | (succ n) := by {
            have s1 : addition 0 n = n, by rw [zero_add n],
            have s2 : addition 0 (succ n) = succ (addition 0 n), from rfl,
            rw [s2, s1]
        }

        lemma add_zero : ∀ (n : ℕ), addition n 0 = n
        | 0 := by refl
        | (succ n) := by refl

        lemma add_one : ∀ n, addition n 1 = succ n
        | 0 := rfl
        | (succ n) := rfl

        lemma one_add : ∀ n, addition 1 n = succ n
        | 0 := by rw [add_zero]
        | (nat.succ npred) := (
            have ih : addition 1 npred = succ npred, from one_add npred,
            have addition 1 (succ npred) = succ (addition 1 npred), from rfl,
            by rw [this, ih]
        )

        lemma m_add_succ (m : ℕ) : ∀ n, addition (succ m) n = succ (addition m n)
        | 0 := rfl
        | (nat.succ npred) := by {
            have ih : addition (succ m) npred = succ (addition m npred), by rw [m_add_succ npred],
            have s1 : addition (succ m) (succ npred) = succ (addition (succ m) npred), from rfl,
            have s2 : succ (addition (succ m) npred) = succ (succ (addition m npred)), by rw [ih],
            have s3 : succ (succ (addition m npred)) = succ (addition m (succ npred)), by refl,
            rw [s1, s2, s3]
        }

        lemma one_add' (n : ℕ): addition 1 n = succ n :=
        have addition 1 n = succ (addition 0 n), by rw m_add_succ,
        by rw [this, zero_add]

        lemma add_succ_commutes : ∀ m n, addition (succ m) n = addition m (succ n)
        | m n := (
            have f1 : addition (succ m) n = succ (addition m n), by rw [m_add_succ m],
            have f2 : addition m (succ n) = succ (addition m n), by rw [addition],
            by simp [f1, f2]
        )

        theorem addition_comm : ∀ (m n : ℕ), addition m n = addition n m
        | 0 n := by rw [add_zero, zero_add]
        | (succ mpred) n :=
            calc
                addition (succ mpred) n = succ (addition mpred n) : by rw m_add_succ
                    ... = succ (addition n mpred) : by rw [addition_comm]
                    ... = addition n (succ mpred) : rfl

        theorem addition_assoc : ∀ (l m n : ℕ), addition (addition l m) n = addition l (addition m n)
        | l m 0 := by rw [add_zero, add_zero]
        | l m (succ npred) :=
            calc
                addition (addition l m) (succ npred) = succ (addition (addition l m) npred) : rfl
                    ... = succ (addition l (addition m npred)) : by rw [addition_assoc]
                    ... = addition l (succ (addition m npred)) : by refl
                    ... = addition l (addition m (succ npred)) : by refl


        -- MULTIPLICATION --

        def multiplication : ℕ → ℕ → ℕ
        | 0 n := 0
        | m 0 := 0
        | m (succ n) := addition (multiplication m n) m

        lemma two_times_three_is_six : multiplication 2 3 = 6 := rfl

        theorem mul_zero : ∀ n, multiplication n 0 = 0
        | 0 := rfl
        | (succ _) := rfl

        theorem zero_mul : ∀ n, multiplication 0 n = 0
        | 0 := rfl
        | (succ _) := rfl

        theorem mul_one : ∀ n, multiplication n 1 = n
        | 0 := rfl
        | (succ n) :=
            calc
                multiplication (succ n) 1 = addition (multiplication (succ n) 0) (succ n) : rfl
                    ... = addition 0 (succ n) : rfl
                    ... = succ n : by rw zero_add

        theorem one_mul : ∀ n, multiplication 1 n = n
        | 0 := rfl
        | (succ n) :=
            calc
                multiplication 1 (succ n) = multiplication 1 n + 1 : rfl
                    ... = n + 1 : by rw [one_mul n]
                    ... = succ n : rfl

        theorem mul_add_once : ∀ m n, addition (multiplication m n) n = multiplication (succ m) n
        | 0 0 := rfl
        | 0 (succ n) := by rw [one_mul, zero_mul, zero_add]
        | (succ m) 0 := by rw [mul_zero, mul_zero, add_zero]
        | (succ m) (succ n) :=
            calc
                addition (multiplication (succ m) (succ n)) (succ n) = addition (addition (multiplication (succ m) n) (succ m)) (succ n) : rfl
                    ... = addition (multiplication (succ m) n) (addition (succ m) (succ n)) : by rw [addition_assoc]
                    ... = addition (multiplication (succ m) n) (addition (succ n) (succ m)) : by rw [addition_comm (succ m)]
                    ... = addition (addition (multiplication (succ m) n) n) (succ (succ m)) : by rw [add_succ_commutes, addition_assoc]
                    ... = addition (multiplication (succ (succ m)) n) (succ (succ m)) : by rw [mul_add_once]
                    ... = multiplication (succ (succ m)) (succ n) : rfl

        theorem mul_comm : ∀ m n, multiplication m n = multiplication n m
        | 0 0 := rfl
        | 0 (succ n) := by rw [zero_mul, mul_zero]
        | (succ m) 0 := by rw [zero_mul, mul_zero]
        | (succ m) (succ n) :=
            calc
                multiplication (succ m) (succ n) = addition (multiplication (succ m) n) (succ m) : rfl
                    ... = addition (multiplication n (succ m)) (succ m) : by rw [mul_comm]
                    ... = multiplication (succ n) (succ m) : by rw [mul_add_once]

        theorem mul_distrib : ∀ l m n, multiplication l (addition m n) = addition (multiplication l m) (multiplication l n)
        | 0 _ _ := by rw [zero_mul, zero_mul, zero_mul, add_zero]
        | _ _ 0 := by rw [add_zero, mul_zero, add_zero]
        | _ 0 _ := by rw [zero_add, mul_zero, zero_add]
        | (l+1) (m+1) (n+1) :=
            let l' := succ l, m' := succ m, n' := succ n in
            -- Looks terrible, could be made much shorter.
            calc
                multiplication l' (addition m' n') = multiplication l' (succ (addition m' n)) : rfl
                    ... = addition (multiplication l' (addition m' n)) l' : rfl
                    ... = addition (multiplication l' (succ $ addition m n)) l' : by { rw [add_succ_commutes], refl }
                    ... = addition (addition (multiplication l' (addition m n)) l') l' : rfl
                    ... = addition (addition (addition (multiplication l (addition m n)) (addition m n)) l') l' : by rw [mul_add_once]
                    ... = addition (addition (addition (addition (multiplication l m) (multiplication l n)) (addition m n)) l') l' : by rw [mul_distrib]
                    ... = addition (addition (addition (multiplication l m) (addition (multiplication l n) (addition m n))) l') l' : by rw [addition_assoc (multiplication l m)]
                    ... = addition (addition (addition (multiplication l m) (addition (addition (multiplication l n) n) m)) l') l' : by rw [addition_comm m n, addition_assoc (multiplication l n)]
                    ... = addition (addition (addition (multiplication l m) (addition (multiplication l' n) m)) l') l' : by rw [mul_add_once]
                    ... = addition (addition (addition (multiplication l m) (addition m (multiplication l' n))) l') l' : by rw [addition_comm (multiplication l' n)]
                    ... = addition (addition (addition (addition (multiplication l m) m) (multiplication l' n)) l') l' : by rw [←addition_assoc (multiplication l m)]
                    ... = addition (addition (addition (multiplication l' m) (multiplication l' n)) l') l' : by rw [mul_add_once]
                    ... = addition (addition (multiplication l' m) (addition (multiplication l' n) l')) l' : by rw [addition_assoc (multiplication l' m)]
                    ... = addition (addition (multiplication l' m) (multiplication l' n')) l' : rfl
                    ... = addition l' (addition (multiplication l' m) (multiplication l' n')) : by rw [addition_comm]
                    ... = addition (addition l' (multiplication l' m)) (multiplication l' n') : by rw [addition_assoc]
                    ... = addition (addition (multiplication l' m) l') (multiplication l' n') : by rw [addition_comm l']
                    ... = addition (multiplication l' m') (multiplication l' n') : rfl

        theorem mul_assoc : ∀ l m n, multiplication (multiplication l m) n = multiplication l (multiplication m n)
        | 0 _ _ := by rw [zero_mul, zero_mul, zero_mul]
        | _ 0 _ := by rw [mul_zero, zero_mul, mul_zero]
        | _ _ 0 := by rw [mul_zero, mul_zero, mul_zero]
        | (l+1) (m+1) (n+1) :=
            let l' := succ l, m' := succ m, n' := succ n in
            -- ditto
            calc
                multiplication (multiplication l' m') n' = addition (multiplication (multiplication l' m') n) (multiplication l' m') : rfl
                    ... = addition (multiplication (addition (multiplication l' m) l') n) (multiplication l' m') : rfl
                    ... = addition (multiplication (addition (addition (multiplication l m) m) l') n) (multiplication l' m') : by rw [mul_add_once]
                    ... = addition (multiplication n (addition (addition (multiplication l m) m) l')) (multiplication l' m') : by rw [mul_comm]
                    ... = addition (addition (multiplication n (addition (multiplication l m) m)) (multiplication n l')) (multiplication l' m') : by rw [mul_distrib n]
                    ... = addition (addition (addition (multiplication n (multiplication l m)) (multiplication n m)) (multiplication n l')) (multiplication l' m') : by rw [mul_distrib n]
                    ... = addition (addition (addition (multiplication (multiplication l m) n) (multiplication n m)) (multiplication n l')) (multiplication l' m') : by rw [mul_comm]
                    ... = addition (addition (addition (multiplication l (multiplication m n)) (multiplication n m)) (multiplication n l')) (multiplication l' m') : by rw [mul_assoc]
                    ... = addition (addition (addition (multiplication l (multiplication m n)) (multiplication m n)) (multiplication n l')) (multiplication l' m') : by rw [mul_comm m]
                    ... = addition (addition (multiplication l' (multiplication m n)) (multiplication n l')) (multiplication l' m') : by rw [mul_add_once]
                    ... = addition (multiplication l' (multiplication m n)) (addition (multiplication n l') (multiplication l' m')) : by rw [addition_assoc]
                    ... = addition (multiplication l' (multiplication m n)) (addition (multiplication l' n) (multiplication l' m')) : by rw [mul_comm n]
                    ... = addition (multiplication l' (multiplication m n)) (multiplication l' (addition n m')) : by rw [mul_distrib]
                    ... = multiplication l' (addition (multiplication m n) (addition n m')) : by rw [←mul_distrib]
                    ... = multiplication l' (addition (multiplication n m) (addition n m')) : by rw [mul_comm m]
                    ... = multiplication l' (addition (addition (multiplication n m) n) m') : by rw [addition_assoc]
                    ... = multiplication l' (addition (addition (multiplication n m) m) n') : by rw [addition_assoc, addition_comm n, add_succ_commutes, ←addition_assoc]
                    ... = multiplication l' (addition (multiplication n' m) n') : by rw [mul_add_once]
                    ... = multiplication l' (multiplication n' m') : by refl
                    ... = multiplication l' (multiplication m' n') : by rw [mul_comm n']


        -- POW --

        def pow (m : ℕ) : ℕ → ℕ
        | 0 := 1
        | (n+1) := multiplication (pow n) m

        theorem pow_2_2_is_4 : pow 2 2 = 4 := rfl
        theorem pow_6_2_is_36 : pow 6 2 = 36 := rfl
        theorem pow_0_1_is_0 : pow 0 1 = 0 := rfl
        theorem pow_n_zero_is_1 (n : ℕ) : pow n 0 = 1 := rfl
        theorem pow_5_3_is_125 : pow 5 3 = 125 := rfl

        theorem pow_0_n_is_0 : ∀ n, (0 < n) → pow 0 n = 0
        | 0 hnpos := by { exact false.elim (lt_irrefl 0 hnpos) }
        | (n+1) _ :=
            calc
                pow 0 (n+1) = multiplication (pow 0 n) 0 : rfl
                    ... = 0 : by rw [mul_zero]

        theorem pow_n_1_is_n : ∀ m, (pow m 1) = m
        | 0 := rfl
        | (m+1) :=
            calc
                pow (m+1) 1 = multiplication (pow m 0) (m+1) : rfl
                    ... = multiplication 1 (m + 1) : rfl
                    ... = m+1 : by rw [one_mul]

        theorem pow_1_n_is_one : ∀ n, pow 1 n = 1
        | 0 := rfl
        | (n+1) :=
            calc
                pow 1 (n+1) = multiplication (pow 1 n) 1 : rfl
                    ... = multiplication 1 1 : by rw [pow_1_n_is_one]
                    ... = 1 : by rw mul_one

        theorem pow_addition_identity : ∀ (b m n : ℕ), pow b (addition m n) = multiplication (pow b m) (pow b n)
        | b 0 0 := by rw [add_zero, pow_n_zero_is_1, mul_one]
        | b (m+1) 0 :=
            calc
                pow b (addition (m+1) 0) = pow b (m+1) : by rw [add_zero]
                    ... = multiplication (pow b (m+1)) 1 : by rw [mul_one]
                    ... = multiplication (pow b (m+1)) (pow 0 0) : by rw [pow_n_zero_is_1]
        | b 0 (n+1) :=
            calc
                pow b (addition 0 (n+1)) = pow b (n+1) : by rw [zero_add]
                    ... = multiplication 1 (pow b (n+1)) : by rw [one_mul]
                    ... = multiplication (pow 0 0) (pow b (n+1)) : by rw [pow_n_zero_is_1]
        | b (m+1) (n+1) :=
            calc
                pow b (addition (m+1) (n+1)) = pow b (succ $ succ $ addition m n) : by rw [m_add_succ, addition_comm m, m_add_succ, addition_comm n]
                    ... = multiplication (multiplication (pow b (addition m n)) b) b : rfl
                    ... = multiplication (multiplication (multiplication (pow b m) (pow b n)) b) b : by rw [pow_addition_identity]
                    ... = multiplication (multiplication (multiplication (pow b m) b) (pow b n)) b : by rw [mul_comm (pow b m), mul_assoc (pow b n), mul_comm (pow b n)]
                    ... = multiplication (multiplication (pow b (m+1)) (pow b n)) b : by refl
                    ... = multiplication (pow b (m+1)) (multiplication (pow b n) b) : by rw [mul_assoc]
                    ... = multiplication (pow b (m+1)) (pow b (n+1)) : by refl

        theorem pow_multiplication_identity : ∀ (b c n : ℕ), pow (multiplication b c) n = multiplication (pow b n) (pow c n)
        | _ _ 0 := by rw [pow_n_zero_is_1, pow_n_zero_is_1, pow_n_zero_is_1, mul_one]
        | b c (n+1) :=
            calc
                pow (multiplication b c) (n+1) = multiplication (pow (multiplication b c) n) (multiplication b c) : rfl
                    ... = multiplication (multiplication (pow b n) (pow c n)) (multiplication b c) : by rw [pow_multiplication_identity]
                    ... = multiplication (pow b n) (multiplication (pow c n) (multiplication b c)) : by rw [mul_assoc]
                    ... = multiplication (pow b n) (multiplication (multiplication (pow c n) c) b) : by rw [mul_comm b, mul_assoc]
                    ... = multiplication (pow b n) (multiplication (pow c (n+1)) b) : by refl
                    ... = multiplication (multiplication (pow b n) b) (pow c (n+1)) : by rw [mul_comm (pow c (n+1)), mul_assoc]
                    ... = multiplication (pow b (n+1)) (pow c (n+1)) : rfl

        theorem pow_pow_identity : ∀ (b m n : ℕ), pow (pow b m) n = pow b (multiplication m n)
        | _ _ 0 := by rw [pow_n_zero_is_1, mul_zero, pow_n_zero_is_1]
        | _ 0 (n+1) := by rw [pow_n_zero_is_1, zero_mul, pow_n_zero_is_1, pow_1_n_is_one]
        | b (m+1) (n+1) :=
            let m' := m+1, n' := n+1 in
            calc
                pow (pow b m') (n+1) = multiplication (pow (pow b m') n) (pow b m') : rfl
                    ... = multiplication (pow b (multiplication m' n)) (pow b m') : by rw [pow_pow_identity]
                    ... = pow b (addition (multiplication m' n) m') : by rw [←pow_addition_identity]
                    ... = pow b (multiplication m' (succ n)) : rfl

    end hidden

end chap8ex2
