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

namespace chap8ex3

    namespace hidden

        variable {α : Type}
        variables (a b c d : α)

        def append : list α → list α → list α
        | [] snd := snd
        | (hd::tl) snd := hd::(append tl snd)

        def reverse : list α → list α
        | [] := []
        | (hd::tl) := append (reverse tl) [hd]

        lemma reverse_abcd : reverse [a, b, c, d] = [d, c, b, a] := rfl

        def length : list α → ℕ
        | [] := 0
        | (hd::tl) := nat.succ $ length tl

        lemma length_abcd : length [a, b, c, d] = 4 := rfl

        def append_nil : ∀ (l: list α), append l [] = l
        | [] := rfl
        | (hd::tl) := calc append (hd::tl) [] = hd::(append tl []) : rfl
            ... = (hd::tl) : by rw [append_nil]

        def nil_append : ∀ (l : list α), append [] l = l
        | [] := rfl
        | (hd::tl) := rfl

        theorem append_lengths : ∀ (l m : list α), length (append l m) = length l + length m
        | l [] := calc
            length (append l []) = length l : by rw [append_nil]
                ... = length l + length [] : rfl
        | [] m := calc
            length (append [] m) = length m : by rw [nil_append]
                ... = 0 + length m : by rw [zero_add]
                ... = length [] + length m : rfl
        | (hd::tl) m :=
            calc length (append (hd::tl) m) = length (hd::(append tl m)) : rfl
                ... = length (append tl m) + 1 : rfl
                ... = (length tl + length m) + 1 : by rw [append_lengths]
                ... = (length tl + 1) + length m : by rw [add_assoc, add_comm (length m), add_assoc]
                ... = length (hd::tl) + length m : rfl


        theorem reverse_preserves_length : ∀ (l : list α), length l = length (reverse l)
        | [] := rfl
        | (hd::tl) := eq.symm $ calc
            length (reverse (hd::tl)) = length (append (reverse tl) [hd]) : rfl
                ... = length (reverse tl) + length [hd] : by rw [append_lengths]
                ... = length tl + 1 : by { rw [reverse_preserves_length tl], refl }
                ... = length (hd::tl) : rfl

    end hidden

end chap8ex3

namespace chap8ex4

    namespace hidden


        variable (C : ℕ → Type)

        #check @nat.rec C

        #check (@nat.below C : ℕ → Type)
        #check nat.below

        #reduce @nat.below C (3 : nat)

        #check (@nat.brec_on C :
        Π (n : ℕ), (Π (n' : ℕ), nat.below C n' → C n') → C n)

        def course_of_value_helper : Π (n : ℕ), (Π (n' : ℕ), nat.below C n' → C n') → nat.below C n
        | 0 _ := ()
        | (n+1) f := ⟨⟨f n (course_of_value_helper n f), course_of_value_helper n f⟩, ()⟩

        def course_of_value : Π (n : ℕ), (Π (n' : ℕ), nat.below C n' → C n') → C n
        | 0 := (
            λ h,
            have f : nat.below C 0 → C 0, from h 0,
            have nat.below C 0, from (),
            f this
        )
        | (n+1) := (
            λ h,
            have f : nat.below C (n+1) → C (n+1), from h (n+1),
            have nat.below C (n+1), from ⟨⟨course_of_value n h, course_of_value_helper C n h⟩, ()⟩,
            f this
        )

        def fib_impl : Π (n : ℕ), nat.below (λ (n : ℕ), ℕ) n → ℕ
        | 0 _ := 1
        | 1 _ := 1
        | (n+2) ⟨⟨fibn, ⟨⟨fibnplus1, _⟩, ()⟩⟩, ()⟩ := by { exact fibn + fibnplus1 }

        def fib : nat → nat := λ n,
        @course_of_value (λ (n : ℕ), ℕ) n (
            λ n' h,
            @fib_impl n' h
        )

        example : fib 0 = 1 := rfl
        example : fib 1 = 1 := rfl
        example : fib 2 = 2 := rfl
        example : fib 3 = 3 := rfl
        example : fib 4 = 5 := rfl
        example : fib 6 = 13 := rfl
    end hidden

    --- Well-founded recursion ---

    namespace hidden
        universes u v
        variable α : Sort u
        variable r : α → α → Prop
        variable h : well_founded r

        variable C : α → Sort (u + 1)
        variable F : Π x, (Π (y : α), r y x → C y) → C x


        #check @well_founded
        #check @acc

        #check (@well_founded.fix : Π {α : Sort u} {C : α → Sort (u + 1)} {r : α → α → Prop},
        well_founded r → (Π (x : α), (Π (y : α), r y x → C y) → C x) → Π (x : α), C x)

        def well_founded_fix (α : Sort u) (C : α → Sort (u + 1)):
        Π {r : α → α → Prop}, well_founded r
        → (Π (x : α), (Π (y : α), r y x → C y) → C x)
        → Π (x : α), C x
        | hr hwellfoundedr hc hx := (
            have hryxtocy : Π (y : α), hr y hx → C y, from (
                λ hy hryx,
                have hr hy hx, from hryx,
                have acc hr hy, from well_founded.apply hwellfoundedr hy,
                acc.rec_on this (λ hz _ f, hc hz f)
            ),
            hc hx hryxtocy
        )

        def f : Π (x : α), C x := well_founded.fix h F
        def f' : Π (x : α), C x := well_founded_fix α C h F
    end hidden

end chap8ex4

namespace chap8ex5

    universe u
    variable {α : Type u}

    inductive vector (α : Type u) : nat → Type u
    | nil {} : vector 0
    | cons   : Π {n}, α → vector n → vector (n+1)

    #print nat.no_confusion
    #print vector.no_confusion
    #check @eq.rec

    namespace vector
        local notation h :: t := cons h t
    end vector

    def vec_zero_plus_n : Π (n : ℕ), vector α n → vector α (0 + n) :=
    λ n v,
    have h1 : vector α (n + 0) := v,
    have h2 : vector α (n + 0) = vector α (0 + n), by rw [add_comm],
    eq.rec h1 h2

    -- With the equation compiler

    def append_with_equation_compiler : Π (m n : ℕ), vector α m → vector α n → vector α (m + n)
    | 0 n vector.nil v2 := vec_zero_plus_n n v2
    | (m+1) n (vector.cons hd tl) v2 := (
        have premise : vector α (m + n), from append_with_equation_compiler m n tl v2,
        have shuffle : vector α (m + n + 1) = vector α (m+1+n), by rw [add_assoc, add_comm n, add_assoc],
        eq.rec (vector.cons hd premise) shuffle
    )

    example : append_with_equation_compiler 2 1 (vector.cons 3 (vector.cons 5 vector.nil)) (vector.cons 8 vector.nil) = vector.cons 3 (vector.cons 5 (vector.cons 8 vector.nil)) := rfl

    -- Without the equation compiler

    def uncons : Π (n : ℕ), vector α (n + 1) → (α × vector α n)
    | _ (vector.cons hd tl) := prod.mk hd tl

    def uncons' : Π (m n : ℕ), vector α m → (m = n + 1) → (α × vector α n) :=
    λ m n v,
    @vector.cases_on
        _
        (λ {m} v, (m = n + 1) → (α × vector α n))
        _
        v
        (λ (h : 0 = n + 1), nat.no_confusion h)
        (λ {n': ℕ} (hd : α) (tl : vector α n'),
            assume (h : n' + 1 = n + 1),
            nat.no_confusion h (
                λ (h1 : n' = n),
                have vector α n' = vector α n, by rw [h1],
                prod.mk hd (eq.rec tl this)
            )
        )


    def append_with_elbow_grease : Π (m n : ℕ), vector α m → vector α n → vector α (m + n) :=
    λ m n v1 v2,
    (
        nat.rec_on m
        (show vector α 0 → vector α (0 + n), from λ _, vec_zero_plus_n n v2)
        (λ (m' : ℕ) (acc : vector α m' → vector α (m' + n)),
            show vector α (m' + 1) → vector α (m' + 1 + n), from (
                λ v,
                let ⟨hd, tl⟩ := uncons' _ m' v rfl in
                have newtl : vector α (m' + n), from acc tl,
                have newvec : vector α (m' + n + 1), from vector.cons hd newtl,
                have shuffle : vector α (m' + n + 1) = vector α ((m' + 1) + n), by rw [add_assoc, add_comm n, add_assoc],
                show vector α (m' + 1 + n), from eq.rec newvec shuffle
            )
        )
    ) v1

    example : append_with_elbow_grease 2 1 (vector.cons 3 (vector.cons 5 vector.nil)) (vector.cons 8 vector.nil) = vector.cons 3 (vector.cons 5 (vector.cons 8 vector.nil)) := rfl

end chap8ex5

namespace chap8ex6

    inductive aexpr : Type
    | const : ℕ → aexpr
    | var : ℕ → aexpr
    | plus : aexpr → aexpr → aexpr
    | times : aexpr → aexpr → aexpr

    open aexpr

    def sample_aexpr : aexpr :=
    plus (times (var 0) (const 7)) (times (const 2) (var 1))

    def aeval (v : ℕ → ℕ) : aexpr → ℕ
    | (const n)    := n
    | (var n)      := v n
    | (plus e₁ e₂)  := aeval e₁ + aeval e₂
    | (times e₁ e₂) := aeval e₁ * aeval e₂

    def sample_val : ℕ → ℕ
    | 0 := 5
    | 1 := 6
    | _ := 0

    -- Try it out. You should get 47 here.
    #eval aeval sample_val sample_aexpr

    def simp_const : aexpr → aexpr
    | (plus (const n₁) (const n₂))  := const (n₁ + n₂)
    | (times (const n₁) (const n₂)) := const (n₁ * n₂)
    | e                             := e

    theorem simp_const_eq' (v : ℕ → ℕ) :
    ∀ e : aexpr, aeval v (simp_const e) = aeval v e :=
    begin
        intros e,
        cases e,
        reflexivity,
        reflexivity,
        cases e_a,
            cases e_a_1,
            repeat { reflexivity },
        cases e_a,
            cases e_a_1,
            repeat { reflexivity },
    end

    theorem simp_const_eq (v : ℕ → ℕ) :
    ∀ e : aexpr, aeval v (simp_const e) = aeval v e
    | (const _) := rfl
    | (var _) := rfl
    | (plus e1 e2) := (
        match e1 with
            | (const m) := (
                match e2 with
                    | (const n) := (
                        have h : simp_const (plus (const m) (const n)) = const (m + n), from rfl,
                        calc
                            aeval v (simp_const (plus (const m) (const n))) = aeval v (const (m + n)) : by rw [h]
                                ... = aeval v (plus (const m) (const n)) : rfl
                    )
                    | (var n) := rfl
                    | (plus e1 e2) := rfl
                    | (times e1 e2) := rfl
                end
            )
            | (var n) := rfl
            | (plus _ _) := rfl
            | (times _ _) := rfl
        end
    )
    | (times e1 e2) := (
        match e1 with
            | (const m) := (
                match e2 with
                    | (const n) := (
                        have h : simp_const (times (const m) (const n)) = const (m * n), from rfl,
                        calc
                            aeval v (simp_const (times (const m) (const n))) = aeval v (const (m * n)) : by rw [h]
                                ... = aeval v (times (const m) (const n)) : rfl
                    )
                    | (var n) := rfl
                    | (plus e1 e2) := rfl
                    | (times e1 e2) := rfl
                end
            )
            | (var n) := rfl
            | (plus _ _) := rfl
            | (times _ _) := rfl
        end
    )

    def fuse : aexpr → aexpr
    | (plus (const n1) (const n2)) := simp_const (plus (const n1) (const n2))
    | (times (const n1) (const n2)) := simp_const (times (const n1) (const n2))
    | (plus e1 e2) := plus (fuse e1) (fuse e2)
    | (times e1 e2) := times (fuse e1) (fuse e2)
    | e := e

    -- This is very repetitive, but I think we need metaprogramming or custom
    -- tactics to address this.
    theorem fuse_eq (v : ℕ → ℕ) :
    ∀ e : aexpr, aeval v (fuse e) = aeval v e :=
    begin
        intro e,
        induction e,
            case const
            { reflexivity },
            case var
            { reflexivity },
            case plus : a b iha ihb
            { cases a,
              cases b,
                reflexivity,
                reflexivity,
                {
                    exact calc
                    aeval v (fuse (plus (const a) (plus b_a b_a_1))) = aeval v (plus (fuse (const a)) (fuse (plus b_a b_a_1))) : rfl
                        ... = aeval v (fuse (const a)) + aeval v (fuse (plus b_a b_a_1)) : rfl
                        ... = aeval v (const a) + aeval v (plus b_a b_a_1) : by rw [iha, ihb]
                        ... = aeval v (plus (const a) (plus b_a b_a_1)) : rfl
                },
                {
                    exact calc
                    aeval v (fuse (plus (const a) (times b_a b_a_1))) = aeval v (plus (fuse (const a)) (fuse (times b_a b_a_1))) : rfl
                        ... = aeval v (fuse (const a)) + aeval v (fuse (times b_a b_a_1)) : rfl
                        ... = aeval v (const a) + aeval v (times b_a b_a_1) : by rw [iha, ihb]
                        ... = aeval v (plus (const a) (times b_a b_a_1)) : rfl
                },
                {
                    exact calc
                        aeval v (fuse (plus (var a) b)) = aeval v (plus (fuse (var a)) (fuse b)) : rfl
                            ... = aeval v (fuse (var a)) + aeval v (fuse b) : rfl
                            ... = aeval v (var a) + aeval v b : by rw [iha, ihb]
                            ... = aeval v (plus (var a) b) : rfl
                },
                {
                    exact calc
                        aeval v (fuse (plus (plus a_a a_a_1) b)) = aeval v (plus (fuse (plus a_a a_a_1)) (fuse b)) : rfl
                            ... = aeval v (fuse (plus a_a a_a_1)) + aeval v (fuse b) : rfl
                            ... = aeval v (plus a_a a_a_1) + aeval v b : by rw [iha, ihb]
                            ... = aeval v (plus (plus a_a a_a_1) b) : rfl
                },
                {
                    exact calc
                        aeval v (fuse (plus (times a_a a_a_1) b)) = aeval v (plus (fuse (times a_a a_a_1)) (fuse b)) : rfl
                            ... = aeval v (fuse (times a_a a_a_1)) + aeval v (fuse b) : rfl
                            ... = aeval v (times a_a a_a_1) + aeval v b : by rw [iha, ihb]
                            ... = aeval v (plus (times a_a a_a_1) b) : rfl
                },
            },
            case times : a b iha ihb
            { cases a,
              cases b,
                reflexivity,
                reflexivity,
                {
                    exact calc
                    aeval v (fuse (times (const a) (plus b_a b_a_1))) = aeval v (times (fuse (const a)) (fuse (plus b_a b_a_1))) : rfl
                        ... = aeval v (fuse (const a)) * aeval v (fuse (plus b_a b_a_1)) : rfl
                        ... = aeval v (const a) * aeval v (plus b_a b_a_1) : by rw [iha, ihb]
                        ... = aeval v (times (const a) (plus b_a b_a_1)) : rfl
                },
                {
                    exact calc
                    aeval v (fuse (times (const a) (times b_a b_a_1))) = aeval v (times (fuse (const a)) (fuse (times b_a b_a_1))) : rfl
                        ... = aeval v (fuse (const a)) * aeval v (fuse (times b_a b_a_1)) : rfl
                        ... = aeval v (const a) * aeval v (times b_a b_a_1) : by rw [iha, ihb]
                        ... = aeval v (times (const a) (times b_a b_a_1)) : rfl
                },
                {
                    exact calc
                        aeval v (fuse (times (var a) b)) = aeval v (times (fuse (var a)) (fuse b)) : rfl
                            ... = aeval v (fuse (var a)) * aeval v (fuse b) : rfl
                            ... = aeval v (var a) * aeval v b : by rw [iha, ihb]
                            ... = aeval v (times (var a) b) : rfl
                },
                {
                    exact calc
                        aeval v (fuse (times (plus a_a a_a_1) b)) = aeval v (times (fuse (plus a_a a_a_1)) (fuse b)) : rfl
                            ... = aeval v (fuse (plus a_a a_a_1)) * aeval v (fuse b) : rfl
                            ... = aeval v (plus a_a a_a_1) * aeval v b : by rw [iha, ihb]
                            ... = aeval v (times (plus a_a a_a_1) b) : rfl
                },
                {
                    exact calc
                        aeval v (fuse (times (times a_a a_a_1) b)) = aeval v (times (fuse (times a_a a_a_1)) (fuse b)) : rfl
                            ... = aeval v (fuse (times a_a a_a_1)) * aeval v (fuse b) : rfl
                            ... = aeval v (times a_a a_a_1) * aeval v b : by rw [iha, ihb]
                            ... = aeval v (times (times a_a a_a_1) b) : rfl
                },
            },
    end

end chap8ex6
