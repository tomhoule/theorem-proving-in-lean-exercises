
-- Working through section 7.1

namespace hidden

    inductive bool : Type
    | ff : bool
    | tt : bool

    def band (b1 b2 : bool) : bool :=
    bool.rec_on b1 bool.ff b2

    theorem t_and_f_is_f : band bool.tt bool.ff = bool.ff := rfl
    theorem f_and_t_is_f : band bool.ff bool.tt = bool.ff := rfl
    theorem f_and_f_is_f : band bool.ff bool.ff = bool.ff := rfl
    theorem t_and_t_is_t : band bool.tt bool.tt = bool.tt := rfl

    def bor (b1 b2 : bool) : bool :=
    bool.rec_on b1 b2 bool.tt

    theorem t_or_t_is_t : bor bool.tt bool.tt = bool.tt := rfl
    theorem t_or_f_is_t : bor bool.tt bool.ff = bool.tt := rfl
    theorem f_or_t_is_t : bor bool.ff bool.tt = bool.tt := rfl
    theorem f_or_f_is_f : bor bool.ff bool.ff = bool.ff := rfl

    def bnot (b : bool) : bool :=
    bool.rec_on b bool.tt bool.ff

    theorem not_t_is_f : bnot bool.tt = bool.ff := rfl
    theorem not_f_is_t : bnot bool.ff = bool.tt := rfl

end hidden

-- Going through section 7.2
--
-- > As exercises, we encourage you to develop a notion of composition for partial functions from α
-- > to β and β to γ, and show that it behaves as expected. We also encourage you to show that bool
-- > and nat are inhabited, that the product of two inhabited types is inhabited, and that the type
-- > of functions to an inhabited type is inhabited.

namespace chap7_section2

    variables { α β γ : Type }
    variables (a : α) (b : β) (c : γ)

    def and_then (f1 : α → option β) (f2 : β → option γ ) (a : α): option γ :=
    have option β, from f1 a,
    show option γ, from option.rec_on this none (λ b, f2 b)

    def return_none (α β : Type) : α → option β := λ _, none
    def return_some (α β : Type) : β → α → option β := λ b a, some b

    theorem none_none_none : and_then (return_none α β) (return_none β γ) a = none := rfl
    theorem none_some_none : and_then (return_none α β) (return_some β γ c) a = none := rfl
    theorem some_none_none : and_then (return_some α β b) (return_none β γ) a = none := rfl
    theorem some_some_some : and_then (return_some α β b) (return_some β γ c) a = some c := rfl

    theorem bool_inhabited : inhabited bool := inhabited.mk tt
    theorem nat_inhabited : inhabited ℕ := inhabited.mk 0
    theorem product_of_inhabited_is_inhabited : inhabited α → inhabited β → inhabited (α × β) :=
        λ alpha beta, inhabited.mk $ prod.mk alpha.default beta.default

    theorem type_of_functions_to_inhabited_type_is_inhabited : inhabited β → inhabited (α → β) :=
        λ hib, inhabited.mk $ λ a, hib.default

end chap7_section2

namespace ch7_section5
    universe u
    variables { α : Type }

    open list

    theorem append_nil (t : list α) : t ++ nil = t :=
    list.rec_on
        t
        (show nil ++ nil = nil, from nil_append (@nil α))
        (λ (hd: α) (tl: list α) (acc : tl ++ nil = tl),
            have e1 : hd::tl ++ nil = hd::(tl ++ nil), from cons_append hd tl nil,
            have e2 : hd::(tl ++ nil) = hd::tl, by rw [acc],
            show hd::tl ++ nil = hd::tl, by rw [e1, e2])

    theorem append_assoc (r s t : list α) :
    r ++ s ++ t = r ++ (s ++ t) :=
    list.rec_on
        r
        (show nil ++ s ++ t = nil ++ (s ++ t), by rw [nil_append, nil_append])
        (λ (hd : α) (tl : list α) (acc : tl ++ s ++ t = tl ++ (s ++ t)),
            calc
                ((hd::tl) ++ s) ++ t = hd::((tl ++ s) ++ t) : cons_append hd (tl ++ s) t
                                 ... = hd::(tl ++ (s ++ t)) : by rw [acc]
                                 ... = (hd::tl) ++ (s ++ t) : by rw [cons_append hd (tl)] )

    -- > Try also defining the function length : Π {α : Type u}, list α → nat that returns the
    -- > length of a list, and prove that it behaves as expected (for example, length (s ++ t) =
    -- > length s + length t).

    def length : list α → ℕ := λ xs, list.rec 0 (λ item list acc, acc + 1) xs

    theorem length_of_nil_is_zero : length (@nil α) = 0 := by refl
    theorem append_length (l1 l2 : list α) : length (l1 ++ l2) = length l1 + length l2 :=
    list.rec_on
        l1
        (
            have f1 : length (nil ++ l2) = length l2, by rw [nil_append],
            have f2 : length (@nil α) + length l2 = length l2, by rw [length_of_nil_is_zero, zero_add],
            show length (nil ++ l2) = length nil + length l2, by rw [f1, f2]
        )
        (λ (hd : α) (tl : list α) (acc : length (tl ++ l2) = length tl + length l2),
            have length (hd::tl) = length tl + 1, by refl,
            eq.symm $
            calc
                length (hd::tl) + length l2 = length tl + length l2 + 1 : by rw [this, add_assoc, add_comm 1, add_assoc]
                                        ... = length (tl ++ l2) + 1 : by rw [acc]
                                        ... = length (hd::tl ++ l2) : by refl
        )


    theorem cons_increases_len_by_1 (a : α) (l : list α) : length (list.cons a l) = length l + 1 := by refl

end ch7_section5

section ch7_section7
    universe u


    theorem mysymm {α : Type u} {a b : α} (h : eq a b) : eq b a :=
    eq.subst h (eq.refl a)

    theorem mytrans {α : Type u} {a b c : α}
    (h₁ : eq a b) (h₂ : eq b c) : eq a c :=
    eq.rec_on h₂ h₁

    theorem mycongr {α β : Type u} {a b : α} (f : α → β)
    (h : eq a b) : eq (f a) (f b) :=
    eq.rec_on h rfl

end ch7_section7

namespace ch7ex1

    def mul (m n : ℕ) : ℕ :=
    nat.rec_on
        n
        nat.zero
        (λ n product, product + m)

    def predecessor (n : ℕ) : ℕ :=
    nat.rec_on
        n
        nat.zero
        (λ n n_pred,
            cond (nat.succ n = 1) nat.zero (nat.succ n_pred)
        )

    def trunc_sub (m n : ℕ) : ℕ :=
    nat.rec_on
        n
        m
        (λ _ running, predecessor running)

    def pow (m n : ℕ) : ℕ :=
    nat.rec_on
        n
        1
        (λ exp running, mul running m)

    theorem n_gt_n_is_absurd (n : ℕ) (n_gt_n : n > n) : false := gt_irrefl n $ n_gt_n

    namespace hidden

        theorem predecessor_succ_n_eq_n (n : ℕ) : predecessor (nat.succ n) = n :=
        nat.rec_on n
            (show predecessor (nat.succ nat.zero) = nat.zero, from rfl)
            (λ n1 eqs, show predecessor (nat.succ (nat.succ n1)) = nat.succ n1, from eq.symm $
                calc
                    nat.succ n1 = nat.succ (predecessor (nat.succ n1)) : by rw eqs
                            ... = predecessor (nat.succ (nat.succ n1)) : by refl
            )

        theorem mul_zero (n : ℕ) : mul n 0 = 0 := rfl
        theorem zero_mul (n : ℕ) : mul 0 n = 0 :=
        nat.rec_on n
            rfl
            (λ n1 eqs,
                calc
                    mul 0 (nat.succ n1) = mul 0 n1 : rfl
                                    ... = 0 : by rw eqs)

        theorem two_times_two : mul 2 2 = 4 := rfl
        theorem two_times_three : mul 2 3 = 6 := rfl

        theorem one_mul (n : ℕ) : mul 1 n = n :=
        nat.rec_on
            n
            (show mul 1 0 = 0, from rfl)
            (λ n eqs,
                calc
                    mul 1 (nat.succ n) = nat.succ (mul 1 n) : rfl
                                   ... = nat.succ n : by rw eqs
            )

        theorem mul_one (n : ℕ) : mul n 1 = n :=
        nat.rec_on n rfl
            (
                λ n eqs,
                    calc
                        mul (nat.succ n) 1 = nat.succ (mul n 1) : rfl
                                       ... = nat.succ n : by rw eqs
            )

        theorem succ_add_eq_add_succ (m n : ℕ) : nat.succ m + n = m + nat.succ n :=
        nat.rec_on n
            (show nat.succ m + nat.zero = nat.succ m, by rw add_zero)
            (
                assume n (hi : nat.succ m + n = m + nat.succ n),
                calc
                    nat.succ m + nat.succ n = m + 1 + nat.succ n : rfl
                        ... = m + (1 + nat.succ n) : by rw add_assoc
                        ... = m + (nat.succ $ nat.succ n) : by rw [add_comm 1]
                        ... = m + nat.succ (nat.succ n) : rfl
            )

        theorem mul_add_once (m n : ℕ) : mul m n + n = mul (nat.succ m) n :=
        nat.rec_on n
            (show mul m 0 + 0 = mul (nat.succ m) 0, from rfl)
            (assume n (hi : mul m n + n = mul (nat.succ m) n),
                -- eq.symm $
                calc
                    mul m (nat.succ n) + (nat.succ n) = mul m n + m + (nat.succ n) : rfl
                        ... = mul m n + (m + nat.succ n) : by rw [add_assoc]
                        ... = mul m n + (nat.succ m + n) : by rw succ_add_eq_add_succ
                        ... = mul m n + n + nat.succ m : by rw [add_comm (nat.succ m) n, add_assoc]
                        ... = mul (nat.succ m) n + nat.succ m : by rw hi
                        ... = mul (nat.succ m) (nat.succ n) : by refl
            )

        theorem mul_comm (m n : ℕ) : mul m n = mul n m :=
        nat.rec_on n
            (show mul m 0 = mul 0 m, by rw [mul_zero, zero_mul])
            (λ n eqs,
                show mul m (nat.succ n) = mul (nat.succ n) m, from calc
                    mul m (nat.succ n) = mul m n + m : rfl
                        ... = (mul n m) + m : by rw eqs
                        ... = mul (nat.succ n) m : by rw mul_add_once
            )

        theorem mul_distrib (l m n : ℕ) : mul l (m + n) = mul l m + mul l n :=
            nat.rec_on n
                (show mul l (m + 0) = mul l m + mul l 0, by repeat { rw add_zero <|> rw mul_zero })
                (assume n (hi : mul l (m + n) = mul l m + mul l n),
                    calc
                        mul l (m + nat.succ n) = mul l (nat.succ (m + n)) : rfl
                            ... = mul l (m + n) + l : rfl
                            ... = (mul l m + mul l n) + l : by rw hi
                            ... = mul l m + (mul l n + l) : by rw add_assoc
                            ... = mul l m + mul l (nat.succ n) : rfl
                )

        theorem mul_assoc (l m n : ℕ) : mul l (mul m n) = mul (mul l m) n :=
        nat.rec_on n
            (show mul l (mul m 0) = mul (mul l m) 0, by { repeat { rw mul_zero <|> rw zero_mul } })
            (assume n (hi : mul l (mul m n) = mul (mul l m) n),
                calc
                    mul l (mul m (nat.succ n)) = mul l ((mul m n) + m) : rfl
                        ... = mul l (mul m n) + mul l m : by rw mul_distrib
                        ... = mul (mul l m) n + mul l m : by rw hi
                        ... = mul (mul l m) (nat.succ n) : rfl
            )

        theorem predecessor_of_zero_is_zero : predecessor 0 = 0 := rfl
        theorem predecessor_of_one_is_zero : predecessor 1 = 0 := rfl
        theorem predecessor_of_two_is_one : predecessor 2 = 1 := rfl
        theorem predecessor_of_thirty_seven_is_thirty_six : predecessor 37 = 36 := rfl

        theorem zero_minus_zero_is_zero : trunc_sub 0 0 = 0 := rfl
        theorem n_minus_zero_is_n (n : ℕ) : trunc_sub n 0 = n := rfl
        theorem thirty_seven_minus_one_is_thirty_six : trunc_sub 37 1 = 36 := rfl
        theorem thirty_seven_minus_twelve_is_twenty_five : trunc_sub 37 12 = 25 := rfl

        theorem pow_2_2_is_4 : pow 2 2 = 4 := rfl
        theorem pow_6_2_is_36 : pow 6 2 = 36 := rfl
        theorem pow_0_1_is_0 : pow 0 1 = 0 := rfl
        theorem pow_n_zero_is_1 (n : ℕ) : pow n 0 = 1 := rfl
        theorem pow_5_3_is_125 : pow 5 3 = 125 := rfl

        theorem pow_n_1_is_n (n : ℕ) : (pow n 1) = n :=
        nat.rec_on n
            (show pow nat.zero 1 = 0, from rfl)
            (λ m m_pow_1_eq_m,
                calc
                    pow (nat.succ m) 1 = mul (pow (nat.succ m) 0) (nat.succ m) : rfl
                                   ... = mul 1 (nat.succ m) : rfl
                                   ... = mul (nat.succ m) 1 : by rw mul_comm
                                   ... = nat.succ m : by rw mul_one
            )

        theorem pow_addition_identity (b m n : ℕ) : pow b (m + n) = mul (pow b m) (pow b n) :=
        nat.rec_on n
            (show pow b (m + 0) = mul (pow b m) (pow b 0), by rw [add_zero, pow_n_zero_is_1, mul_one])
            (assume n (hi : pow b (m + n) = mul (pow b m) (pow b n)),
                calc
                    pow b (m + nat.succ n) = pow b (nat.succ (m + n)) : rfl
                        ... = mul (pow b (m + n)) b : rfl
                        ... = mul (mul (pow b m) (pow b n)) b : by rw hi
                        ... = mul (pow b m) (mul (pow b n) b) : by rw [mul_assoc]
                        ... = mul (pow b m) (pow b (nat.succ n)) : rfl
            )


        example (b m n : ℕ) : pow (pow b m) n = pow b (mul m n) :=
            nat.rec_on n
                (show pow (pow b m) 0 = pow b (mul m 0), by repeat { rw mul_zero <|> rw pow_n_zero_is_1 })
                (assume n (hi : pow (pow b m) n = pow b (mul m n)),
                    calc
                        pow (pow b m) (nat.succ n) = mul (pow (pow b m) n) (pow b m) : rfl
                            ... = mul (pow b (mul m n)) (pow b m) : by rw hi
                            ... = pow b (mul m n + m) : by rw pow_addition_identity
                            ... = pow b (mul m (nat.succ n)) : rfl
                )

        example (b c n : ℕ) : pow (mul b c) n = mul (pow b n) (pow c n) :=
            nat.rec_on n
                (show pow (mul b c) 0 = mul (pow b 0) (pow c 0), by { rw [pow_n_zero_is_1, pow_n_zero_is_1, pow_n_zero_is_1], refl })
                (assume n (hi : pow (mul b c) n = mul (pow b n) (pow c n)),
                    calc
                        pow (mul b c) (nat.succ n) = mul (pow (mul b c) n) (mul b c) : rfl
                            ... = mul (mul (pow b n) (pow c n)) (mul b c) : by rw hi
                            ... = mul (mul (mul (pow c n) (pow b n)) b) c : by rw [mul_assoc, mul_comm (pow b n)]
                            ... = mul (mul (pow c n) (mul (pow b n) b)) c : by rw [mul_assoc]
                            ... = mul (mul (pow c n) (pow b (nat.succ n))) c : rfl
                            ... = mul (mul (pow b (nat.succ n)) (pow c n)) c : by rw [mul_comm (pow b (nat.succ n))]
                            ... = mul (pow b (nat.succ n)) (mul (pow c n) c) : by rw mul_assoc
                            ... = mul (pow b (nat.succ n)) (pow c (nat.succ n)) : rfl

                )

    end hidden

end ch7ex1

namespace ch7ex2
    open ch7_section5

    variables { α : Type }

    def reverse (xs : list α) : list α :=
    list.rec_on xs
        list.nil
        (assume x (xs: list α) (hi : list α), list.append hi (list.cons x list.nil))

    theorem nil_append (xs : list α) : list.nil ++ xs = xs := rfl
    theorem reverse_nil : reverse (@list.nil α) = @list.nil α := rfl

    theorem reverse_append (xs ys : list α) : reverse (xs ++ ys) = reverse ys ++ reverse xs :=
    list.rec_on xs
        (show reverse (list.nil ++ ys) = reverse ys ++ list.nil, by rw [nil_append, append_nil])
        (assume hd (tl : list α) (hi : reverse (tl ++ ys) = reverse ys ++ reverse tl),
            calc
                reverse ((hd::tl) ++ ys) = reverse (hd::(tl ++ ys)) : rfl
                    ... = reverse (tl ++ ys) ++ (hd::list.nil) : rfl
                    ... = (reverse ys ++ reverse tl) ++ (hd::list.nil) : by rw hi
                    ... = reverse ys ++ (reverse tl ++ (hd::list.nil)) : by rw append_assoc
                    ... = reverse ys ++ reverse (hd::tl) : rfl
        )

    theorem basic_append (a b c d : α) :
        reverse (list.cons a (list.cons b (list.cons c (list.cons d list.nil)))) = list.cons d (list.cons c (list.cons b (list.cons a list.nil))) :=
            rfl

    theorem reverse_preserves_length (xs : list α) : length (reverse xs) = length xs :=
    list.rec_on xs
        (show length (reverse list.nil) = length list.nil, by rw reverse_nil)
        (assume hd (tl : list α) (hi : length (reverse tl) = length tl),
            calc
                length (reverse $ hd::tl) = length ((reverse tl) ++ (hd::list.nil)) : rfl
                    ... = length (reverse tl) + length (hd::list.nil) : by rw append_length
                    ... = length tl + 1 : by { rw hi, refl }
                    ... = length (hd::tl) : rfl
        )

    theorem reverse_twice_is_id (xs : list α) : reverse (reverse xs) = xs :=
    list.rec_on xs
        (show reverse (reverse list.nil) = list.nil, from rfl)
        (assume hd (xs : list α) (hi : reverse (reverse xs) = xs),
            calc
                reverse (reverse $ hd::xs) = reverse ((reverse xs) ++ (hd::list.nil)) : rfl
                    ... = reverse (hd::list.nil) ++ (reverse $ reverse xs) : by rw reverse_append
                    ... = hd::(reverse $ reverse xs) : rfl
                    ... = hd::xs : by rw hi
            -- show reverse (reverse $ hd::xs) = hd::xs, from sorry
        )

end ch7ex2

namespace ch7ex3

    inductive Expr : Type
    | const (n : ℕ) : Expr
    | var (n : ℕ) : Expr
    | plus (s t : Expr) : Expr
    | times (s t : Expr) : Expr


    def eval (vars : list ℕ) (expr : Expr) : option ℕ :=
    Expr.rec_on expr
        (λ hn, hn)
        (λ idx, vars.nth idx)
        (λ hs ht hseval hteval,
            have product : option (ℕ × ℕ), from option.bind hseval (λ ha, option.map (λ hb, ⟨ha, hb⟩) hteval ),
            option.map (λ (h : ℕ × ℕ), h.1 + h.2) product
        )
        (λ hs ht hseval hteval,
            have product : option (ℕ × ℕ), from option.bind hseval (λ ha, option.map (λ hb, (ha, hb)) hteval),
            option.map (λ (h : ℕ × ℕ), h.1 * h.2) product
        )

    theorem const_2_is_2 : eval [] (Expr.const 2) = option.some 2 := rfl
    theorem simple_var_assignment : eval [5] (Expr.var 0) = option.some 5 := rfl
    theorem missing_vars_fail_evaluation : eval [5, 8] (Expr.var 4) = option.none := rfl
    theorem addition_with_variable : eval [12] (Expr.plus (Expr.const 2) (Expr.var 0)) = some 14 := rfl
    theorem addition_and_multiplication_with_variables : eval [4, 10] (Expr.times (Expr.var 1) (Expr.plus (Expr.const 5) (Expr.var 0))) = some 90 := rfl

end ch7ex3

namespace ch7ex4

    inductive Proposition : Type
    | false : Proposition
    | var (n : ℕ) : Proposition
    | not (p : Proposition) : Proposition
    | and (p q : Proposition) : Proposition
    | or (p q : Proposition) : Proposition

    def eval (vars : list bool) (formula : Proposition) : option bool :=
    begin
        induction formula,
            case Proposition.false
                { exact bool.ff },
            case Proposition.var : n
                { exact vars.nth n },
            case Proposition.not
                { exact option.map (λ h, bool.rec_on h bool.tt bool.ff) formula_ih },
            case Proposition.and
                {
                    have : option (bool × bool), from option.bind  formula_ih_p (λ hp, option.map (λ hq, (hp, hq)) formula_ih_q),
                    exact option.map (λ (hpq : bool × bool), bool.rec_on hpq.1 bool.ff hpq.2) this
                 },
            case Proposition.or
                {
                    have : option (bool × bool), from option.bind  formula_ih_p (λ hp, option.map (λ hq, (hp, hq)) formula_ih_q),
                    exact option.map (λ (hpq : bool × bool), bool.rec_on hpq.1 hpq.2 bool.tt) this
                 },
    end

    def complexity (formula : Proposition) : ℕ :=
    begin
        induction formula,
            case Proposition.false
                { exact 1 },
            case Proposition.var
                { exact 1 },
            case Proposition.not
                { exact 1 + formula_ih },
            case Proposition.and : p q
                { exact formula_ih_p + formula_ih_q + 1 },
            case Proposition.or : p q
                { exact formula_ih_p + formula_ih_q + 1 },
    end

    def substitute (varnum : ℕ) (formula subst : Proposition) : Proposition :=
    begin
        induction formula,
            case Proposition.false
                { exact Proposition.false },
            case Proposition.var : n
                { exact cond (varnum = n) subst (Proposition.var n) },
            case Proposition.not : p
                { exact Proposition.not formula_ih },
            case Proposition.and : p q
                { exact Proposition.and formula_ih_p formula_ih_q },
            case Proposition.or : p q
                { exact Proposition.or formula_ih_p formula_ih_q },
    end

    lemma substitute_works : substitute 1 (Proposition.or (Proposition.false) (Proposition.var 1)) (Proposition.not Proposition.false) = Proposition.or Proposition.false (Proposition.not Proposition.false) := rfl

end ch7ex4

namespace ch7ex5

    inductive even : ℕ → bool → Prop
    | zero : even 0 tt
    | even_succ : ∀ (n : ℕ), even n ff → even (n + 1) tt
    | odd_succ : ∀ (n : ℕ), even n tt → even (n + 1) ff

    lemma zero_is_even : even 0 tt := even.zero
    lemma one_is_odd : even 1 ff := even.odd_succ 0 even.zero
    lemma two_is_even : even 2 tt := even.even_succ 1 one_is_odd
    lemma three_is_odd : even 3 ff := even.odd_succ 2 two_is_even

end ch7ex5
