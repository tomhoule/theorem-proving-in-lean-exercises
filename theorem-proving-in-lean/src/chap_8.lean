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

    end hidden

end chap8ex2
