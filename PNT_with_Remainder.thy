theory PNT_with_Remainder
imports
  "Prime_Number_Theorem.Prime_Counting_Functions"
begin

abbreviation nat_powr
  (infixr "nat'_powr" 80)
where
  "n nat_powr x \<equiv> (of_nat n) powr x"
definition "logderiv f x \<equiv> deriv f x / f x"
definition log_differentiable
  (infixr "(log'_differentiable)" 50)
where
  "f log_differentiable x \<equiv> (f field_differentiable (at x)) \<and> f x \<noteq> 0"
abbreviation "mangoldt_real :: _ \<Rightarrow> real \<equiv> mangoldt"
abbreviation "mangoldt_complex :: _ \<Rightarrow> complex \<equiv> mangoldt"
abbreviation "fds_zeta_complex :: complex fds \<equiv> fds_zeta"

bundle pnt_notation
begin
notation norm ("\<parallel>_\<parallel>")
notation Suc ("_\<^sub>+" [101] 100)
end

bundle no_pnt_notation
begin
no_notation norm ("\<parallel>_\<parallel>")
no_notation Suc ("_\<^sub>+" [101] 100)
end

unbundle pnt_notation
unbundle "prime_counting_notation"

section \<open>Implication relation of many forms of prime number theorem\<close>

definition rem_est :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> _" where
"rem_est c m n \<equiv> O(\<lambda> x. x * exp (-c * ln x powr m * ln (ln x) powr n))"

definition Li :: "real \<Rightarrow> real" where "Li x \<equiv> integral {2..x} (\<lambda>x. 1 / ln x)"
definition PNT_1 where "PNT_1 c m n \<equiv> ((\<lambda>x. \<pi> x - Li x) \<in> rem_est c m n)"
definition PNT_2 where "PNT_2 c m n \<equiv> ((\<lambda>x. \<theta> x - x) \<in> rem_est c m n)"
definition PNT_3 where "PNT_3 c m n \<equiv> ((\<lambda>x. \<psi> x - x) \<in> rem_est c m n)"

hide_fact Equivalence_Measurable_On_Borel.integral_combine
hide_fact Equivalence_Lebesgue_Henstock_Integration.integral_reflect_real

lemma exp_bigo:
  fixes f g :: "real \<Rightarrow> real"
  assumes "\<forall>\<^sub>F x in at_top. f x \<le> g x"
  shows "(\<lambda>x. exp (f x)) \<in> O(\<lambda>x. exp (g x))"
proof -
  from assms have "\<forall>\<^sub>F x in at_top. exp (f x) \<le> exp (g x)" by simp
  hence "\<forall>\<^sub>F x in at_top. \<parallel>exp (f x)\<parallel> \<le> 1 * \<parallel>exp (g x)\<parallel>" by simp
  thus ?thesis by blast
qed

lemma rem_est_compare_powr:
  fixes c m n :: real
  assumes h: "0 < m" "m < 1"
  shows "(\<lambda>x. x powr (2 / 3)) \<in> rem_est c m n"
proof -
  have "\<forall>\<^sub>F x in at_top. c * (ln x) powr m * ln (ln x) powr n \<le> 1 / 3 * (ln x)"
    using h by real_asymp
  hence *: "(\<lambda>x. exp (c * ln x powr m * ln (ln x) powr n)) \<in> O(\<lambda>x. x powr (1 / 3))"
    by (simp add: exp_bigo powr_def)
  have "(\<lambda>x :: real. x powr (2 / 3)) \<in> O(\<lambda>x. x * x powr (-1 / 3))" by real_asymp
  moreover have "(\<lambda>x :: real. x * x powr (-1 / 3)) \<in> rem_est c m n"
    unfolding rem_est_def using * by (simp add: landau_o.big.inverse exp_minus powr_minus)
  ultimately show ?thesis
    unfolding rem_est_def by (rule landau_o.big.trans)
qed

lemma PNT_3_imp_PNT_2:
  fixes c m n :: real
  assumes h: "0 < m" "m < 1" and "PNT_3 c m n"
  shows "PNT_2 c m n"
proof -
  have 1: "(\<lambda> x. \<psi> x - x) \<in> rem_est c m n"
    using assms(3) unfolding PNT_3_def by auto
  have "(\<lambda>x. \<psi> x - \<theta> x) \<in> O(\<lambda>x. ln x * sqrt x)" by (rule \<psi>_minus_\<theta>_bigo)
  moreover have "(\<lambda>x. ln x * sqrt x) \<in> O(\<lambda>x. x powr (2 / 3))" by real_asymp
  ultimately have 2: "(\<lambda>x. \<psi> x - \<theta> x) \<in> rem_est c m n"
    using rem_est_compare_powr [OF h, of c n] unfolding rem_est_def
    by (blast intro: landau_o.big.trans)
  have "(\<lambda>x. \<psi> x - x - (\<psi> x - \<theta> x)) \<in> rem_est c m n"
    using 1 2 unfolding rem_est_def by (rule sum_in_bigo)
  thus ?thesis unfolding PNT_2_def by simp
qed

lemma integrable_cut':
  fixes a b c :: real and f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "b \<le> c"
  and Hf: "\<And>x. a \<le> x \<Longrightarrow> f integrable_on {a..x}"
  shows "f integrable_on {b..c}"
proof -
  have "a \<le> c" using assms by linarith
  hence "f integrable_on {a..c}" by (rule Hf)
  thus ?thesis by
    (rule integrable_subinterval_real)
    (subst subset_iff, (subst atLeastAtMost_iff)+,
    blast intro: \<open>a \<le> b\<close> order_trans [of a b])
qed

lemma integral_bigo:
  fixes a :: real and f g :: "real \<Rightarrow> real"
  assumes f_bound: "f \<in> O(g)"
    and Hf:  "\<And>x. a \<le> x \<Longrightarrow> f integrable_on {a..x}"
    and Hf': "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) integrable_on {a..x}"
    and Hg': "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. \<bar>g x\<bar>) integrable_on {a..x}"
  shows "(\<lambda>x. integral{a..x} f) \<in> O(\<lambda>x. 1 + integral{a..x} (\<lambda>x. \<bar>g x\<bar>))"
proof -
  from \<open>f \<in> O(g)\<close> obtain c where "\<forall>\<^sub>F x in at_top. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>"
    unfolding bigo_def by auto
  then obtain N' :: real where asymp: "\<And>n. n\<ge>N' \<Longrightarrow> \<bar>f n\<bar> \<le> c * \<bar>g n\<bar>"
    by (subst (asm) eventually_at_top_linorder) (blast)
  define N where "N \<equiv> max a N'"
  define I where "I \<equiv> \<bar>integral {a..N} f\<bar>"
  define J where "J \<equiv> integral {a..N} (\<lambda>x. \<bar>g x\<bar>)"
  define c' where "c' \<equiv> max (I + J * \<bar>c\<bar>) \<bar>c\<bar>"
  have "\<And>x. N \<le> x \<Longrightarrow> \<bar>integral {a..x} f\<bar>
      \<le> c' * \<bar>1 + integral {a..x} (\<lambda>x. \<bar>g x\<bar>)\<bar>"
  proof -
    fix x :: real
    assume 1: "N \<le> x"
    define K where "K \<equiv> integral {a..x} (\<lambda>x. \<bar>g x\<bar>)"
    have 2: "a \<le> N" unfolding N_def by linarith
    hence 3: "a \<le> x" using 1 by linarith
    have nnegs: "0 \<le> I" "0 \<le> J" "0 \<le> K"
      unfolding I_def J_def K_def using 1 2 Hg'
      by (auto intro!: integral_nonneg)
    hence abs_eq: "\<bar>I\<bar> = I" "\<bar>J\<bar> = J" "\<bar>K\<bar> = K"
      using nnegs by simp+
    have "integral\<bar>f\<bar>": "(\<lambda>x. \<bar>f x\<bar>) integrable_on {N..x}"
      using 2 1 Hf' by (rule integrable_cut')
    have "integralf": "f integrable_on {N..x}"
      using 2 1 Hf by (rule integrable_cut')
    have "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. c * \<bar>g x\<bar>) integrable_on {a..x}"
      by (blast intro: Hg' integrable_cmul [OF Hg', simplified])
    hence "integralc\<bar>g\<bar>": "(\<lambda>x. c * \<bar>g x\<bar>) integrable_on {N..x}"
      using 2 1 by (blast intro: integrable_cut')
    have "\<bar>integral {a..x} f\<bar> \<le> I + \<bar>integral {N..x} f\<bar>"
      unfolding I_def
      by (subst integral_combine[OF 2 1 Hf [of x], THEN sym])
         (rule 3, rule abs_triangle_ineq)
    also have "\<dots> \<le> I + integral {N..x} (\<lambda>x. \<bar>f x\<bar>)"
    proof -
      note integral_norm_bound_integral [OF "integralf" "integral\<bar>f\<bar>"]
      then have "\<bar>integral {N..x} f\<bar> \<le> integral {N..x} (\<lambda>x. \<bar>f x\<bar>)" by auto
      then show ?thesis by linarith
    qed also have "\<dots> \<le> I + c * integral {N..x} (\<lambda>x. \<bar>g x\<bar>)"
    proof -
      have 1: "N' \<le> N" unfolding N_def by linarith
      hence "\<And>y :: real. N \<le> y \<Longrightarrow> \<bar>f y\<bar> \<le> c * \<bar>g y\<bar>"
      proof -
        fix y :: real
        assume "N \<le> y"
        thus "\<bar>f y\<bar> \<le> c * \<bar>g y\<bar>"
          by (rule asymp [OF order_trans [OF 1]])
      qed
      hence "integral {N..x} (\<lambda>x. \<bar>f x\<bar>) \<le> integral {N..x} (\<lambda>x. c * \<bar>g x\<bar>)"
        by (rule integral_le [OF "integral\<bar>f\<bar>" "integralc\<bar>g\<bar>"], simp)
      thus ?thesis by simp
    qed also have "\<dots> \<le> I + \<bar>c\<bar> * (J + integral {a..x} (\<lambda>x. \<parallel>g x\<parallel>))"
    proof simp
      note integral_combine[OF 2 1 Hg' [of x]]
      hence K_min_J: "integral {N..x} (\<lambda>x. \<bar>g x\<bar>) = K - J"
        unfolding J_def K_def using 3 by auto
      have "c * (K - J) \<le> \<bar>c\<bar> * (J + K)" proof -
        have "c * (K - J) \<le> \<bar>c * (K - J)\<bar>" by simp
        also have "\<dots> = \<bar>c\<bar> * \<bar>K - J\<bar>" by (simp add: abs_mult)
        also have "\<dots> \<le> \<bar>c\<bar> * (\<bar>J\<bar>+\<bar>K\<bar>)" by (simp add: mult_left_mono)
        finally show ?thesis by (simp add: abs_eq)
      qed
      thus "c * integral {N..x} (\<lambda>x. \<bar>g x\<bar>)
        \<le> \<bar>c\<bar> * (J + integral {a..x} (\<lambda>x. \<bar>g x\<bar>))"
      by (subst K_min_J, fold K_def)
    qed
    also have "\<dots> \<le> c' * \<bar>1 + integral {a..x} (\<lambda>x. \<bar>g x\<bar>)\<bar>"
    by (subst (2) abs_of_nonneg,
        simp add: integral_nonneg Hg' 3,
        simp add: field_simps,
        subst add.assoc [symmetric],
        rule add_mono, unfold c'_def, auto,
        rule mult_right_mono, auto,
        fold K_def, rule nnegs)
    finally show "\<bar>integral {a..x} f\<bar>
      \<le> c' * \<bar>1 + integral {a..x} (\<lambda>x. \<bar>g x\<bar>)\<bar>".
  qed
  note 0 = this
  show ?thesis proof (rule eventually_mono [THEN bigoI])
    show "\<forall>\<^sub>Fx in at_top. N \<le> x" by simp
    show "\<And>x. N \<le> x \<Longrightarrow> \<parallel>integral {a..x} f\<parallel> \<le> c' * 
      \<parallel>1 + integral {a..x} (\<lambda>x. \<bar>g x\<bar>)\<parallel>" by (simp, rule 0)
  qed
qed

definition r\<^sub>1 where "r\<^sub>1 x \<equiv> \<pi> x - Li x" for x
definition r\<^sub>2 where "r\<^sub>2 x \<equiv> \<theta> x - x" for x

lemma pi_represent_by_theta:
  fixes x :: real
  assumes "2 \<le> x"
  shows "\<pi> x = \<theta> x / (ln x) + integral {2..x} (\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2))"
proof -
  note integral_unique [OF \<pi>_conv_\<theta>_integral]
  with assms show ?thesis by auto
qed

theorem integration_by_part':
  fixes a b :: real
    and f g :: "real \<Rightarrow> 'a :: {real_normed_field, banach}"
    and f' g' :: "real \<Rightarrow> 'a"
  assumes "a \<le> b"
    and "\<And>x. x \<in> {a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
    and "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
    and int: "(\<lambda>x. f x * g' x) integrable_on {a..b}"
  shows "((\<lambda>x. f' x * g x) has_integral
    f b * g b - f a * g a - integral{a..b} (\<lambda>x. f x * g' x)) {a..b}"
proof -
  define prod where "prod \<equiv> (*) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  define y where "y \<equiv> f b * g b - f a * g a - integral{a..b} (\<lambda>x. f x * g' x)"
  have 0: "bounded_bilinear prod" unfolding prod_def
    by (rule bounded_bilinear_mult)
  have 1: "((\<lambda>x. f x * g' x) has_integral f b * g b - f a * g a - y) {a..b}"
  using y_def and int and integrable_integral by auto
  note 2 = integration_by_parts
    [where y = y and prod = prod, OF 0, unfolded prod_def]
  have "continuous_on {a..b} f" "continuous_on {a..b} g"
    by (auto intro: has_vector_derivative_continuous
                    has_vector_derivative_at_within assms
             simp: continuous_on_eq_continuous_within)
  with assms and 1 show ?thesis by (fold y_def, intro 2) auto
qed

lemma Li_integrate_by_part:
  fixes x :: real
  assumes "2 \<le> x"
  shows
  "(\<lambda>x. 1 / (ln x)\<^sup>2) integrable_on {2..x}"
  "Li x = x / (ln x) - 2 / (ln 2) + integral {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2)"
proof -
  have 1: "\<And>y :: real. 2 \<le> y \<Longrightarrow>
    DERIV (\<lambda>t. 1 / (ln t)) y :> - (1 / (y * (ln y)\<^sup>2))"
  proof -
    fix y :: real assume Hy: "2 \<le> y"
    define a where "a \<equiv> (0 * ln y - 1 * (1 / y))/(ln y * ln y)"
    have "DERIV (\<lambda>t. 1 / (ln t)) y :> a"
    unfolding a_def
    proof (rule derivative_intros DERIV_ln_divide)+
      from Hy show "0 < y" by linarith
      note ln_gt_zero and Hy thus "ln y \<noteq> 0" by auto
    qed
    also have "a = -1 / (y * (ln y)\<^sup>2)"
      unfolding a_def by (simp add: power2_eq_square)
    finally show "DERIV (\<lambda>t. 1 / (ln t)) y :> - (1 / (y * (ln y)\<^sup>2))" by auto
  qed
  have 2: "(\<lambda>x. x * (- 1 / (x * (ln x)\<^sup>2))) integrable_on {2..x}"
    by (rule integrable_continuous_interval)
       ((rule continuous_intros)+, auto)
  have "((\<lambda>x. 1 * (1 / ln x)) has_integral
    x * (1 / ln x) - 2 * (1 / ln 2) - integral {2..x} (\<lambda>x. x * (- 1 / (x * (ln x)\<^sup>2)))
    ) {2..x}"
    by (rule integration_by_part', auto, rule \<open>2 \<le> x\<close>,
        subst has_real_derivative_iff_has_vector_derivative [symmetric],
        auto intro: 1, rule 2 [simplified])
  note 3 = this [simplified]
  have "((\<lambda>x. 1 / ln x) has_integral (x / ln x - 2 / ln 2 + integral {2..x} (\<lambda>x. 1 / (ln x)\<^sup>2))) {2..x}"
  proof -
    define a where "a t \<equiv> if t = 0 then 0 else 1 / (ln t)\<^sup>2" for t :: real
    have "\<And>t :: real. t \<in> {2..x} \<Longrightarrow> a t = 1 / (ln t)\<^sup>2"
      unfolding a_def by auto
    hence 4: "integral {2..x} a = integral {2..x} (\<lambda>x. 1 / (ln x)\<^sup>2)" by (rule integral_cong)
    from 3 show ?thesis
      by (subst (asm) 4 [unfolded a_def])
  qed
  thus "Li x = x / ln x - 2 / ln 2 + integral {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2)" unfolding Li_def by auto
  show "(\<lambda>x. 1 / (ln x)\<^sup>2) integrable_on {2..x}"
    by (rule integrable_continuous_interval)
       ((rule continuous_intros)+, auto)
qed

theorem \<theta>_integrable:
  fixes x :: "real"
  assumes "2 \<le> x"
  shows "(\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2)) integrable_on {2..x}"
by (rule \<pi>_conv_\<theta>_integral [THEN has_integral_integrable], rule assms)

lemma r\<^sub>1_represent_by_r\<^sub>2:
  fixes x :: real
  assumes Hx: "2 \<le> x"
  shows "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) integrable_on {2..x}" (is ?P)
    "r\<^sub>1 x = r\<^sub>2 x / (ln x) + 2 / ln 2 + integral {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))" (is ?Q)
proof -
  have 0: "\<And>t. t \<in> {2..x} \<Longrightarrow> (\<theta> t - t) / (t * (ln t)\<^sup>2) = \<theta> t / (t * (ln t)\<^sup>2) - 1 / (ln t)\<^sup>2"
    by (subst diff_divide_distrib, auto)
  note integrables = \<theta>_integrable Li_integrate_by_part(1)
  let ?D = "integral {2..x} (\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2)) -
    integral {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2)"
  have "((\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2) - 1 / (ln t)\<^sup>2) has_integral
    ?D) {2..x}"
  unfolding r\<^sub>2_def by
    (rule has_integral_diff)
    (rule integrables [THEN integrable_integral], rule Hx)+
  hence 0: "((\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) has_integral
    ?D) {2..x}"
  unfolding r\<^sub>2_def by (subst has_integral_cong [OF 0])
  thus ?P by (rule has_integral_integrable)
  note 1 = 0 [THEN integral_unique]
  have 2: "r\<^sub>2 x / ln x = \<theta> x / ln x - x / ln x"
    unfolding r\<^sub>2_def by (rule diff_divide_distrib)
  from pi_represent_by_theta and Li_integrate_by_part(2) and assms
  have "\<pi> x - Li x = \<theta> x / ln x
    + integral {2..x} (\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2))
    - (x / ln x - 2 / ln 2 + integral {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2))"
    by auto
  also have "\<dots> = r\<^sub>2 x / ln x + 2 / ln 2
    + integral {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))"
    by (subst 2, subst 1) auto
  finally show ?Q unfolding r\<^sub>1_def by auto
qed

lemma eventually_at_top_linorderI':
  fixes c :: "'a :: {no_top, linorder}"
  assumes h: "\<And>x. c < x \<Longrightarrow> P x"
  shows "eventually P at_top"
proof (rule eventually_mono)
  show "\<forall>\<^sub>F x in at_top. c < x" by (rule eventually_gt_at_top)
  from h show "\<And>x. c < x \<Longrightarrow> P x" .
qed

lemma smallo_ln_diverge_1:
  fixes f :: "real \<Rightarrow> real"
  assumes f_ln: "f \<in> o(ln)"
  shows "LIM x at_top. x * exp (- f x) :> at_top"
proof -
  have "(1/2 :: real) > 0" by auto
  with f_ln have 0: "\<forall>\<^sub>F x in at_top. \<parallel>f x\<parallel> \<le> 1/2 * \<parallel>ln x\<parallel>" unfolding smallo_def by fast
  have "x * exp (-f x) \<ge> x powr (1/2)"
    if 1:"1 \<le> x" and 2:"\<parallel>f x\<parallel> \<le> 1/2 * \<parallel>ln x\<parallel>" for x
  proof -
    have "f x \<le> \<parallel>f x\<parallel>" by auto
    also have "\<dots> \<le> 1/2 * \<parallel>ln x\<parallel>" by (rule 2)
    also have "\<dots> \<le> 1/2 * ln x" using 1 by auto
    finally have 0: "f x \<le> 1/2 * ln x" by auto
    have "x powr (-1/2) = exp (-1/2 * ln x)"
      unfolding powr_def using 1 by auto
    also have "\<dots> \<le> exp (-f x)" using 0 by auto
    finally have 0: "x powr (-1/2) \<le> exp (-f x)" .
    have "x powr (1/2) = x powr (1 + -1/2)" by auto
    also have "\<dots> = x powr 1 * x powr (-1/2)" by (rule powr_add)
    also have "\<dots> = x * x powr (-1/2)" using 1 by auto
    also have "\<dots> \<le> x * exp (-f x)" using 0 1 by auto
    finally show ?thesis .
  qed
  hence "\<forall>\<^sub>F x in at_top. \<parallel>f x\<parallel> \<le> 1/2 * \<parallel>ln x\<parallel> \<longrightarrow> x * exp (-f x) \<ge> x powr (1/2)"
    by (blast intro: eventually_at_top_linorderI)
  hence 0: "\<forall>\<^sub>F x in at_top. x * exp (-f x) \<ge> x powr (1/2)"
    by (rule eventually_rev_mp [OF 0])
  show "LIM x at_top. x * exp (- f x) :> at_top"
    by (rule filterlim_at_top_mono [OF _ 0], real_asymp)
qed

lemma exp_integral_asymp:
  fixes f f' :: "real \<Rightarrow> real"
  assumes cf: "continuous_on {a..} f"
      and der: "\<And>x. a < x \<Longrightarrow> DERIV f x :> f' x"
      and td: "((\<lambda>x. x * f' x) \<longlongrightarrow> 0) at_top"
      and f_ln: "f \<in> o(ln)"
  shows "(\<lambda>x. integral {a..x} (\<lambda>t. exp (-f t))) \<sim>[at_top] (\<lambda>x. x * exp(-f x))"
proof (rule asymp_equivI', rule lhospital_at_top_at_top)
  have cont_exp: "continuous_on {a..} (\<lambda>t. exp (- f t))"
    using cf by (intro continuous_intros)
  show "\<forall>\<^sub>F x in at_top. ((\<lambda>x. integral {a..x} (\<lambda>t. exp (- f t)))
    has_real_derivative exp (- f x)) (at x)" (is "eventually ?P ?F")
  proof (rule eventually_at_top_linorderI')
    fix x assume 1: "a < x"
    hence 2: "a \<le> x" by linarith
    have 3: "(at x within {a..x+1}) = (at x)"
      by (rule at_within_interior, auto, rule 1)
    show "?P x"
      by (subst 3 [symmetric], rule integral_has_real_derivative)
         (rule continuous_on_subset [OF cont_exp], auto, rule 2)
  qed
  have "\<forall>\<^sub>F x in at_top. ((\<lambda>x. x * exp (- f x))
    has_real_derivative 1 * exp (- f x) + exp (- f x) * (- f' x) * x) (at x)"
    (is "eventually ?P ?F")
  proof (rule eventually_at_top_linorderI')
    fix x assume 1: "a < x"
    hence 2: "(at x within {a<..}) = (at x)" by (auto intro: at_within_open)
    show "?P x"
      by (subst 2 [symmetric], intro derivative_intros)
         (subst 2, rule der, rule 1)
  qed
  moreover have
    "1 * exp (- f x) + exp (- f x) * (- f' x) * x
    = exp (- f x) * (1 - x * f' x)" for x :: real
    by (simp add: field_simps)
  ultimately show "\<forall>\<^sub>F x in at_top.
       ((\<lambda>x. x * exp (- f x))
    has_real_derivative exp (- f x) * (1 - x * f' x)) (at x)" by auto
  show "LIM x at_top. x * exp (- f x) :> at_top"
    using f_ln by (rule smallo_ln_diverge_1)
  have "((\<lambda>x. 1 / (1 - x * f' x)) \<longlongrightarrow> 1 / (1 - 0)) at_top"
    by ((rule tendsto_intros)+, rule td, linarith)
  thus "((\<lambda>x. exp (- f x) / (exp (- f x) * (1 - x * f' x))) \<longlongrightarrow> 1) at_top" by auto
  have "((\<lambda>x. 1 - x * f' x) \<longlongrightarrow> 1 - 0) at_top"
    by ((rule tendsto_intros)+, rule td)
  hence 0: "((\<lambda>x. 1 - x * f' x) \<longlongrightarrow> 1) at_top" by simp
  hence "\<forall>\<^sub>F x in at_top. 0 < 1 - x * f' x"
    by (rule order_tendstoD) linarith
  moreover have "\<forall>\<^sub>F x in at_top. 0 < 1 - x * f' x \<longrightarrow> exp (- f x) * (1 - x * f' x) \<noteq> 0" by auto
  ultimately show "\<forall>\<^sub>F x in at_top. exp (- f x) * (1 - x * f' x) \<noteq> 0"
    by (rule eventually_rev_mp)
qed

lemma x_mul_exp_larger_than_const:
  fixes c :: real and g :: "real \<Rightarrow> real"
  assumes g_ln: "g \<in> o(ln)"
  shows "(\<lambda>x. c) \<in> O(\<lambda>x. x * exp(-g x))"
proof -
  have "LIM x at_top. x * exp (- g x) :> at_top"
    using g_ln by (rule smallo_ln_diverge_1)
  hence "\<forall>\<^sub>F x in at_top. 1 \<le> x * exp (- g x)"
    using filterlim_at_top by fast
  hence "\<forall>\<^sub>F x in at_top. \<parallel>c\<parallel> * 1 \<le> \<parallel>c\<parallel> * \<parallel>x * exp (- g x)\<parallel>"
    by (rule eventually_rev_mp)
       (auto simp del: mult_1_right
             intro!: eventuallyI mult_left_mono)
  thus "(\<lambda>x. c :: real) \<in> O(\<lambda>x. x * exp (- g x))" by auto
qed

lemma integral_bigo_exp':
  fixes a :: real and f g g' :: "real \<Rightarrow> real"
  assumes f_bound: "f \<in> O(\<lambda>x. exp(-g x))"
    and Hf:   "\<And>x. a \<le> x \<Longrightarrow> f integrable_on {a..x}"
    and Hf':  "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) integrable_on {a..x}"
    and Hg:   "continuous_on {a..} g"
    and der:  "\<And>x. a < x \<Longrightarrow> DERIV g x :> g' x"
    and td:   "((\<lambda>x. x * g' x) \<longlongrightarrow> 0) at_top"
    and g_ln: "g \<in> o(ln)"
  shows "(\<lambda>x. integral{a..x} f) \<in> O(\<lambda>x. x * exp(-g x))"
proof -
  have "\<And>y. (\<lambda>x. exp(-g x)) integrable_on {a..y}"
    by (rule integrable_continuous_interval,
       (rule continuous_intros)+,
        rule continuous_on_subset, rule Hg, auto)
  hence "\<And>y. (\<lambda>x. \<bar>exp(-g x)\<bar>) integrable_on {a..y}" by simp
  hence "(\<lambda>x. integral{a..x} f) \<in> O(\<lambda>x. 1 + integral{a..x} (\<lambda>x. \<bar>exp(-g x)\<bar>))"
    using assms by (intro integral_bigo)
  hence "(\<lambda>x. integral{a..x} f) \<in> O(\<lambda>x. 1 + integral{a..x} (\<lambda>x. exp(-g x)))" by simp
  also have "(\<lambda>x. 1 + integral{a..x} (\<lambda>x. exp(-g x))) \<in> O(\<lambda>x. x * exp(-g x))"
  proof (rule sum_in_bigo)
    show "(\<lambda>x. 1 :: real) \<in> O(\<lambda>x. x * exp (- g x))"
      by (intro x_mul_exp_larger_than_const g_ln)
    show "(\<lambda>x. integral {a..x} (\<lambda>x. exp (- g x))) \<in> O(\<lambda>x. x * exp (- g x))"
      by (rule asymp_equiv_imp_bigo, rule exp_integral_asymp, auto intro: assms)
  qed
  finally show ?thesis .
qed

lemma integral_bigo_exp:
  fixes a b :: real and f g g' :: "real \<Rightarrow> real"
  assumes le: "a \<le> b"
    and f_bound: "f \<in> O(\<lambda>x. exp(-g x))"
    and Hf:  "\<And>x. a \<le> x \<Longrightarrow> f integrable_on {a..x}"
    and Hf': "\<And>x. b \<le> x \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) integrable_on {b..x}"
    and Hg:  "continuous_on {b..} g"
    and der: "\<And>x. b < x \<Longrightarrow> DERIV g x :> g' x"
    and td:  "((\<lambda>x. x * g' x) \<longlongrightarrow> 0) at_top"
    and g_ln:"g \<in> o(ln)"
  shows "(\<lambda>x. integral {a..x} f) \<in> O(\<lambda>x. x * exp(-g x))"
proof -
  have "(\<lambda>x. integral {a..b} f) \<in> O(\<lambda>x. x * exp(-g x))"
    by (intro x_mul_exp_larger_than_const g_ln)
  moreover have "(\<lambda>x. integral {b..x} f) \<in> O(\<lambda>x. x * exp(-g x))"
    by (intro integral_bigo_exp' [where ?g' = g']
              f_bound Hf Hf' Hg der td g_ln)
       (use le Hf integrable_cut' in auto)
  ultimately have "(\<lambda>x. integral {a..b} f + integral {b..x} f) \<in> O(\<lambda>x. x * exp(-g x))"
    by (rule sum_in_bigo)
  moreover have "integral {a..x} f = integral {a..b} f + integral {b..x} f" when "b \<le> x" for x
    by (subst eq_commute, rule integral_combine)
       (insert le that, auto intro: Hf)
  hence "\<forall>\<^sub>F x in at_top. integral {a..x} f = integral {a..b} f + integral {b..x} f"
    by (rule eventually_at_top_linorderI)
  ultimately show ?thesis
    by (rule_tac landau_o.big.ev_eq_trans2)
qed

lemma set_integrableI_bounded:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "A \<in> sets M
  \<Longrightarrow> (\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable M
  \<Longrightarrow> emeasure M A < \<infinity>
  \<Longrightarrow> (AE x in M. x \<in> A \<longrightarrow> norm (f x) \<le> B)
  \<Longrightarrow> set_integrable M A f"
unfolding set_integrable_def
  by (rule integrableI_bounded_set[where A=A]) auto

lemma ln_when_ge_3:
  "1 < ln x" if "3 \<le> x" for x :: real
proof (rule ccontr)
  assume "\<not> 1 < ln x"
  hence "exp (ln x) \<le> exp 1" by auto
  hence "x \<le> exp 1" using that by auto
  thus False using e_less_272 that by auto
qed

lemma integrate_r\<^sub>2_estimate:
  fixes c m n :: real
  assumes hm: "0 < m" "m < 1"
    and h: "r\<^sub>2 \<in> rem_est c m n"
  shows "(\<lambda>x. integral {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))) \<in> rem_est c m n"
unfolding rem_est_def
proof (subst mult.assoc,
       subst minus_mult_left [symmetric],
       rule integral_bigo_exp)
  show "(2 :: real) \<le> 3" by auto
  show "(\<lambda>x. c * (ln x powr m * ln (ln x) powr n)) \<in> o(ln)"
    using hm by real_asymp
  have "ln x \<noteq> 1" when "3 \<le> x" for x :: real
    using ln_when_ge_3 [of x] that by auto
  thus "continuous_on {3..} (\<lambda>x. c * (ln x powr m * ln (ln x) powr n))"
    by (intro continuous_intros) auto
  show "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) integrable_on {2..x}"
    if "2 \<le> x" for x using that by (rule r\<^sub>1_represent_by_r\<^sub>2(1))
  define g where "g x \<equiv>
    c * (m * ln x powr (m - 1) * (1 / x * 1) * ln (ln x) powr n
       + n * ln (ln x) powr (n - 1) * (1 / ln x * (1 / x)) * ln x powr m)"
    for x
  show "((\<lambda>x. c * (ln x powr m * ln (ln x) powr n)) has_real_derivative g x) (at x)"
    if "3 < x" for x
  proof -
    have *: "at x within {3<..} = at x"
      by (rule at_within_open, auto, rule that)
    moreover have
      "((\<lambda>x. c * (ln x powr m * ln (ln x) powr n)) has_real_derivative g x)
       (at x within {3<..})"
    unfolding g_def using that
    by (intro derivative_intros DERIV_mult DERIV_cmult)
       (auto intro: ln_when_ge_3 DERIV_ln_divide simp add: *)
    ultimately show ?thesis by auto
  qed
  show "((\<lambda>x. x * g x) \<longlongrightarrow> 0) at_top"
    unfolding g_def using hm by real_asymp
  have nz: "\<forall>\<^sub>F t :: real in at_top. t * (ln t)\<^sup>2 \<noteq> 0"
  proof (rule eventually_at_top_linorderI')
    fix x :: real assume "1 < x"
    thus "x * (ln x)\<^sup>2 \<noteq> 0" by auto
  qed
  define h where "h x \<equiv> exp (- c * ln x powr m * ln (ln x) powr n)" for x
  have "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) \<in> O(\<lambda>x. (x * h x) / (x * (ln x)\<^sup>2))"
    by (rule landau_o.big.divide_right, rule nz)
       (unfold h_def, fold rem_est_def, rule h)
  also have "(\<lambda>x. (x * h x) / (x * (ln x)\<^sup>2)) \<in> O(\<lambda>x. h x)"
  proof -
    have "(\<lambda>x :: real. 1 / (ln x)\<^sup>2) \<in> O(\<lambda>x. 1)" by real_asymp
    hence "(\<lambda>x. h x * (1 / (ln x)\<^sup>2)) \<in> O(\<lambda>x. h x * 1)"
      by (rule landau_o.big.mult_left)
    thus ?thesis
      by (auto simp add: field_simps
               intro!: landau_o.big.ev_eq_trans2)
         (auto intro: eventually_at_top_linorderI [of 1])
  qed
  finally show "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))
    \<in> O(\<lambda>x. exp (- (c * (ln x powr m * ln (ln x) powr n))))"
    unfolding h_def by (simp add: algebra_simps)
  have "(\<lambda>x. r\<^sub>2 x / (x * (ln x)\<^sup>2)) absolutely_integrable_on {2..x}"
    if *:"2 \<le> x" for x
  proof (rule set_integrableI_bounded, auto)
    show "emeasure lborel {2..x} < top_class.top" using * by auto
    have "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2) * indicator {2..x} t) \<in> borel_measurable lebesgue"
      using * by (intro integrable_integral
        [THEN has_integral_implies_lebesgue_measurable_real])
        (rule r\<^sub>1_represent_by_r\<^sub>2(1))
    thus "(\<lambda>xa. indicator {2..x} xa * r\<^sub>2 xa / (xa * (ln xa)\<^sup>2)) \<in> borel_measurable lebesgue"
      by (simp add: mult_ac)
    let ?C = "(ln 4 + 1) / (ln 2)\<^sup>2 :: real"
    show "AE xa in lebesgue. 2 \<le> xa \<and> xa \<le> x \<longrightarrow> \<bar>r\<^sub>2 xa\<bar> / (xa * (ln xa)\<^sup>2) \<le> ?C"
    proof (rule AE_I2, auto)
      fix t assume "2 \<le> t" "t \<le> x"
      hence h: "1 \<le> t" "2 \<le> t" by linarith+
      hence "0 \<le> \<theta> t \<and> \<theta> t < ln 4 * t" by (auto intro: \<theta>_upper_bound)
      hence *:"\<bar>\<theta> t\<bar> \<le> ln 4 * t" by auto
      have "1 \<le> ln t / ln 2" using h by auto
      hence "1 \<le> (ln t / ln 2)\<^sup>2" by auto
      also have "\<dots> = (ln t)\<^sup>2 / (ln 2)\<^sup>2" unfolding power2_eq_square by auto
      finally have "1 \<le> (ln t)\<^sup>2 / (ln 2)\<^sup>2" .
      hence "\<bar>r\<^sub>2 t\<bar> \<le> \<bar>\<theta> t\<bar> + \<bar>t\<bar>" unfolding r\<^sub>2_def by auto
      also have "\<dots> \<le> ln 4 * t + 1 * t" using h * by auto
      also have "\<dots> = (ln 4 + 1) * t" by (simp add: algebra_simps)
      also have "\<dots> \<le> (ln 4 + 1) * t * ((ln t)\<^sup>2 / (ln 2)\<^sup>2)"
        by (auto simp add: field_simps)
           (rule add_mono; rule rev_mp[OF h(2)], auto)
      finally have *:"\<bar>r\<^sub>2 t\<bar> \<le> ?C * (t * (ln t)\<^sup>2)" by auto
      thus "\<bar>r\<^sub>2 t\<bar> / (t * (ln t)\<^sup>2) \<le> ?C"
        using h * by (auto simp add: field_simps)
    qed
  qed
  hence "\<And>x. 2 \<le> x \<Longrightarrow> (\<lambda>x. \<bar>r\<^sub>2 x / (x * (ln x)\<^sup>2)\<bar>) integrable_on {2..x}"
    by (fold real_norm_def)
       (rule absolutely_integrable_on_def [THEN iffD1, THEN conjunct2])
  thus "\<And>x. 3 \<le> x \<Longrightarrow> (\<lambda>x. \<bar>r\<^sub>2 x / (x * (ln x)\<^sup>2)\<bar>) integrable_on {3..x}"
    by (rule_tac integrable_cut' [where ?a = 2]) simp
qed

lemma r\<^sub>2_div_ln_estimate:
  fixes c m n :: real
  assumes hm: "0 < m" "m < 1"
    and h: "r\<^sub>2 \<in> rem_est c m n"
  shows "(\<lambda>x. r\<^sub>2 x / (ln x) + 2 / ln 2) \<in> rem_est c m n"
proof -
  have "(\<lambda>x. r\<^sub>2 x / ln x) \<in> O(r\<^sub>2)"
  proof (intro bigoI eventually_at_top_linorderI)
    fix x :: real assume 1:"exp 1 \<le> x"
    have 2:"(0 :: real) < exp 1" by simp
    hence 3:"0 < x" using 1 by linarith
    have 4: "0 \<le> \<bar>r\<^sub>2 x\<bar>" by auto
    have "(1 :: real) = ln (exp 1)" by simp
    also have "\<dots> \<le> ln x" using 1 2 3 by (subst ln_le_cancel_iff)
    finally have "1 \<le> ln x" .
    thus "\<parallel>r\<^sub>2 x / ln x\<parallel> \<le> 1 * \<parallel>r\<^sub>2 x\<parallel>"
      by (auto simp add: field_simps, subst mult_le_cancel_right1, auto)
  qed
  with h have 1: "(\<lambda>x. r\<^sub>2 x / ln x) \<in> rem_est c m n"
    unfolding rem_est_def by (rule_tac landau_o.big.trans)
  moreover have "(\<lambda>x :: real. 2 / ln 2) \<in> O(\<lambda>x. x powr (2 / 3))"
    by real_asymp
  hence "(\<lambda>x :: real. 2 / ln 2) \<in> rem_est c m n"
    using rem_est_compare_powr [OF hm, of c n]
    unfolding rem_est_def by (rule landau_o.big.trans)
  ultimately show ?thesis
    unfolding rem_est_def by (rule sum_in_bigo)
qed

lemma PNT_2_imp_PNT_1:
  fixes l :: real
  assumes h: "0 < m" "m < 1" and "PNT_2 c m n"
  shows "PNT_1 c m n"
proof -
  from assms(3) have h': "r\<^sub>2 \<in> rem_est c m n"
    unfolding PNT_2_def r\<^sub>2_def by auto
  let ?a = "\<lambda>x. r\<^sub>2 x / ln x + 2 / ln 2"
  let ?b = "\<lambda>x. integral {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))"
  have 1: "\<forall>\<^sub>F x in at_top. \<pi> x - Li x = ?a x + ?b x"
    by (rule eventually_at_top_linorderI, fold r\<^sub>1_def)
       (rule r\<^sub>1_represent_by_r\<^sub>2(2), blast)
  have 2: "(\<lambda>x. ?a x + ?b x) \<in> rem_est c m n"
    by (unfold rem_est_def, (rule sum_in_bigo; fold rem_est_def))
       (intro r\<^sub>2_div_ln_estimate integrate_r\<^sub>2_estimate h h')+
  from landau_o.big.in_cong [OF 1] and 2 show ?thesis
    unfolding PNT_1_def rem_est_def by blast
qed

lemma PNT_3_imp_PNT_1:
  fixes l :: real
  assumes h : "0 < m" "m < 1" and "PNT_3 c m n"
  shows "PNT_1 c m n"
  by (intro PNT_2_imp_PNT_1 PNT_3_imp_PNT_2 assms)

unbundle no_prime_counting_notation

section \<open>Some basic theorems in complex analysis\<close>

lemma holomorphic_glue_to_analytic:
  assumes o: "open S" "open T"
     and hf: "f holomorphic_on S"
     and hg: "g holomorphic_on T"
     and hI: "\<And>z. z \<in> S \<Longrightarrow> z \<in> T \<Longrightarrow> f z = g z"
     and hU: "U \<subseteq> S \<union> T"
  obtains h
   where "h analytic_on U"
         "\<And>z. z \<in> S \<Longrightarrow> h z = f z"
         "\<And>z. z \<in> T \<Longrightarrow> h z = g z"
proof -
  define h where "h z \<equiv> if z \<in> S then f z else g z" for z
  show ?thesis proof
    have "h holomorphic_on S \<union> T"
      unfolding h_def by (rule holomorphic_on_If_Un) (use assms in auto)
    thus "h analytic_on U"
      by (subst analytic_on_holomorphic) (use hU o in auto)
  next
    fix z assume *:"z \<in> S"
    show "h z = f z" unfolding h_def using * by auto
  next
    fix z assume *:"z \<in> T"
    show "h z = g z" unfolding h_def using * hI by auto
  qed
qed

definition not_zero_on (infixr "not'_zero'_on" 46)
  where "f not_zero_on S \<equiv> \<exists>z \<in> S. f z \<noteq> 0"

lemma not_zero_on_obtain:
  assumes "f not_zero_on S" and "S \<subseteq> T"
  obtains t where "f t \<noteq> 0" and "t \<in> T"
using assms unfolding not_zero_on_def by auto

theorem analytic_on_holomorphic_connected:
  assumes hf: "f analytic_on S"
    and con: "connected A"
    and ne: "\<xi> \<in> A" and AS: "A \<subseteq> S"
  obtains T T' where
    "f holomorphic_on T" "f holomorphic_on T'"
    "open T" "open T'" "A \<subseteq> T" "S \<subseteq> T'" "connected T"
proof -
  obtain T'
  where oT': "open T'" and sT': "S \<subseteq> T'"
    and holf': "f holomorphic_on T'"
    using analytic_on_holomorphic hf by blast
  define T where "T \<equiv> connected_component_set T' \<xi>"
  have TT': "T \<subseteq> T'" unfolding T_def by (rule connected_component_subset)
  hence holf: "f holomorphic_on T" using holf' by auto
  have opT: "open T" unfolding T_def using oT' by (rule open_connected_component)
  have conT: "connected T" unfolding T_def by (rule connected_connected_component)
  have "A \<subseteq> T'" using AS sT' by blast
  hence AT: "A \<subseteq> T" unfolding T_def using ne con by (intro connected_component_maximal)
  show ?thesis using holf holf' opT oT' AT sT' conT that by blast
qed

theorem analytic_factor_zero:
  assumes hf: "f analytic_on S"
    and KS: "K \<subseteq> S" and con: "connected K"
    and \<xi>K: "\<xi> \<in> K" and \<xi>z: "f \<xi> = 0"
    and nz: "f not_zero_on K"
  obtains g r n
    where "0 < n" "0 < r"
          "g analytic_on S" "g not_zero_on K"
          "\<And>z. z \<in> S \<Longrightarrow> f z = (z - \<xi>)^n * g z"
          "\<And>z. z \<in> ball \<xi> r \<Longrightarrow> g z \<noteq> 0"
proof -
  have "f analytic_on S" "connected K"
       "\<xi> \<in> K" "K \<subseteq> S" using assms by auto
  then obtain T T'
  where holf: "f holomorphic_on T"
    and holf': "f holomorphic_on T'"
    and opT: "open T" and oT': "open T'"
    and KT: "K \<subseteq> T" and ST': "S \<subseteq> T'"
    and conT: "connected T"
    by (rule analytic_on_holomorphic_connected)
  obtain \<eta> where f\<eta>: "f \<eta> \<noteq> 0" and \<eta>K: "\<eta> \<in> K"
    using nz by (rule not_zero_on_obtain, blast)
  hence \<xi>T: "\<xi> \<in> T" and \<xi>T': "\<xi> \<in> T'"
    and \<eta>T: "\<eta> \<in> T" using \<xi>K \<eta>K KT KS ST' by blast+
  hence nc: "\<not> f constant_on T" using f\<eta> \<xi>z unfolding constant_on_def by fastforce
  obtain g r n
  where 1: "0 < n" and 2: "0 < r"
    and bT: "ball \<xi> r \<subseteq> T"
    and hg: "g holomorphic_on ball \<xi> r"
    and fw: "\<And>z. z \<in> ball \<xi> r \<Longrightarrow> f z = (z - \<xi>) ^ n * g z"
    and gw: "\<And>z. z \<in> ball \<xi> r \<Longrightarrow> g z \<noteq> 0"
    by (rule holomorphic_factor_zero_nonconstant, (rule holf opT conT \<xi>T \<xi>z nc)+, blast)
  have sT: "S \<subseteq> T' - {\<xi>} \<union> ball \<xi> r" using 2 ST' by auto
  have hz: "(\<lambda>z. f z / (z - \<xi>) ^ n) holomorphic_on (T' - {\<xi>})"
    using holf' by ((intro holomorphic_intros)+, auto)
  obtain h
   where 3: "h analytic_on S"
     and hf: "\<And>z. z \<in> T' - {\<xi>} \<Longrightarrow> h z = f z / (z - \<xi>) ^ n"
     and hb: "\<And>z. z \<in> ball \<xi> r \<Longrightarrow> h z = g z"
    by (rule holomorphic_glue_to_analytic
       [where f = "\<lambda>z. f z / (z - \<xi>) ^ n" and
         g = g and S = "T' - {\<xi>}" and T = "ball \<xi> r" and U = S])
       (use oT' 2 ST' hg fw hz in \<open>auto simp add: holomorphic_intros\<close>)
  have "\<xi> \<in> ball \<xi> r" using 2 by auto
  hence "h \<xi> \<noteq> 0" using hb gw 2 by auto
  hence 4: "h not_zero_on K" unfolding not_zero_on_def using \<xi>K by auto
  have 5: "f z = (z - \<xi>)^n * h z" if *: "z \<in> S" for z
  proof -
    consider "z = \<xi>" | "z \<in> S - {\<xi>}" using * by auto
    thus ?thesis proof cases
      assume *: "z = \<xi>"
      show ?thesis using \<xi>z 1 by (subst (1 2) *, auto)
    next
      assume *: "z \<in> S - {\<xi>}"
      show ?thesis using hf ST' * by (auto simp add: field_simps)
    qed
  qed
  have 6: "\<And>w. w \<in> ball \<xi> r \<Longrightarrow> h w \<noteq> 0" using hb gw by auto
  show ?thesis by ((standard; rule 1 2 3 4 5 6), blast+)
qed

theorem analytic_compact_finite_zeros:
  assumes af: "f analytic_on S"
    and KS: "K \<subseteq> S"
    and con: "connected K"
    and cm: "compact K"
    and nz: "f not_zero_on K"
  shows "finite {z \<in> K. f z = 0}"
proof (cases "f constant_on K")
  assume *: "f constant_on K"
  have "\<And>z. z \<in> K \<Longrightarrow> f z \<noteq> 0" using nz * unfolding not_zero_on_def constant_on_def by auto
  hence **: "{z \<in> K. f z = 0} = {}" by auto
  thus ?thesis by (subst **, auto)
next
  assume *: "\<not> f constant_on K"
  obtain \<xi> where ne: "\<xi> \<in> K" using not_zero_on_obtain nz by blast
  obtain T T' where opT: "open T" and conT: "connected T"
    and ST: "K \<subseteq> T" and holf: "f holomorphic_on T"
    and "f holomorphic_on T'"
    by (metis af KS con ne analytic_on_holomorphic_connected)
  have "\<not> f constant_on T" using ST * unfolding constant_on_def by blast
  thus ?thesis using holf opT conT cm ST by (intro holomorphic_compact_finite_zeros)
qed

definition analytic_factor_p' where
 \<open>analytic_factor_p' f S K \<equiv>
  \<exists>g n. \<exists>\<alpha> :: nat \<Rightarrow> complex.
        g analytic_on S
      \<and> (\<forall>z \<in> K. g z \<noteq> 0)
      \<and> (\<forall>z \<in> S. f z = g z * (\<Prod>k<n. z - \<alpha> k))
      \<and> \<alpha> ` {..<n} \<subseteq> K\<close>

definition analytic_factor_p where
 \<open>analytic_factor_p F \<equiv>
  \<forall>f S K. f analytic_on S
    \<longrightarrow> K \<subseteq> S
    \<longrightarrow> connected K
    \<longrightarrow> compact K
    \<longrightarrow> f not_zero_on K
    \<longrightarrow> {z \<in> K. f z = 0} = F
    \<longrightarrow> analytic_factor_p' f S K\<close>

theorem analytic_factorization_E:
  shows "analytic_factor_p {}"
unfolding analytic_factor_p_def
proof (intro conjI allI impI)
  fix f S K
  assume af: "f analytic_on S"
     and KS: "K \<subseteq> S"
     and con: "connected K"
     and cm: "compact K"
     and nz: "{z \<in> K. f z = 0} = {}"
  show "analytic_factor_p' f S K"
  unfolding analytic_factor_p'_def
  proof (intro ballI conjI exI)
    show "f analytic_on S" "\<And>z. z \<in> K \<Longrightarrow> f z \<noteq> 0"
         "\<And>z. z \<in> S \<Longrightarrow> f z = f z * (\<Prod>k<(0 :: nat). z - (\<lambda>_. 0) k)"
      by (rule af, use nz in auto)
    show "(\<lambda>k :: nat. 0) ` {..<0} \<subseteq> K" by auto
  qed
qed

theorem analytic_factorization_I:
  assumes ind: "analytic_factor_p F"
    and \<xi>ni: "\<xi> \<notin> F"
  shows "analytic_factor_p (insert \<xi> F)"
unfolding analytic_factor_p_def
proof (intro allI impI)
  fix f S K
  assume af: "f analytic_on S"
    and KS: "K \<subseteq> S"
    and con: "connected K"
    and nz: "f not_zero_on K"
    and cm: "compact K"
    and zr: "{z \<in> K. f z = 0} = insert \<xi> F"
  show "analytic_factor_p' f S K"
  proof -
    have "f analytic_on S" "K \<subseteq> S" "connected K"
         "\<xi> \<in> K" "f \<xi> = 0" "f not_zero_on K"
    using af KS con zr nz by auto
    then obtain h r k
    where "0 < k" and "0 < r" and ah: "h analytic_on S"
      and nh: "h not_zero_on K"
      and f_z: "\<And>z. z \<in> S \<Longrightarrow> f z = (z - \<xi>) ^ k * h z"
      and ball: "\<And>z. z \<in> ball \<xi> r \<Longrightarrow> h z \<noteq> 0"
    by (rule analytic_factor_zero) blast
    hence h\<xi>: "h \<xi> \<noteq> 0" using ball by auto
    hence "\<And>z. z \<in> K \<Longrightarrow> h z = 0 \<longleftrightarrow> f z = 0 \<and> z \<noteq> \<xi>" by (subst f_z) (use KS in auto)
    hence "{z \<in> K. h z = 0} = {z \<in> K. f z = 0} - {\<xi>}" by auto
    also have "\<dots> = F" by (subst zr, intro Diff_insert_absorb \<xi>ni)
    finally have "{z \<in> K. h z = 0} = F" .
    hence "analytic_factor_p' h S K"
      using ind ah KS con cm nh
      unfolding analytic_factor_p_def by auto
    then obtain g n and \<alpha> :: "nat \<Rightarrow> complex"
    where ag: "g analytic_on S" and
      ng: "\<And>z. z \<in> K \<Longrightarrow> g z \<noteq> 0" and
      h_z: "\<And>z. z \<in> S \<Longrightarrow> h z = g z * (\<Prod>k<n. z - \<alpha> k)" and
      Im\<alpha>: "\<alpha> ` {..<n} \<subseteq> K"
    unfolding analytic_factor_p'_def by fastforce
    define \<beta> where "\<beta> j \<equiv> if j < n then \<alpha> j else \<xi>" for j
    show ?thesis
    unfolding analytic_factor_p'_def
    proof (intro ballI conjI exI)
      show "g analytic_on S" "\<And>z. z \<in> K \<Longrightarrow> g z \<noteq> 0"
        by (rule ag, rule ng)
    next
      fix z assume *: "z \<in> S"
      show "f z = g z * (\<Prod>j<n+k. z - \<beta> j)"
      proof -
        have "(\<Prod>j<n. z - \<beta> j) = (\<Prod>j<n. z - \<alpha> j)"
            "(\<Prod>j=n..<n+k. z - \<beta> j) = (z - \<xi>) ^ k"
        unfolding \<beta>_def by auto
        moreover have "(\<Prod>j<n+k. z - \<beta> j) = (\<Prod>j<n. z - \<beta> j) * (\<Prod>j=n..<n+k. z - \<beta> j)"
        by (metis Metric_Arith.nnf_simps(8) atLeast0LessThan
           not_add_less1 prod.atLeastLessThan_concat zero_order(1))
        ultimately have "(\<Prod>j<n+k. z - \<beta> j) = (z - \<xi>) ^ k * (\<Prod>j<n. z - \<alpha> j)" by auto
        moreover have "f z = g z * ((z - \<xi>) ^ k * (\<Prod>j<n. z - \<alpha> j))"
        by (subst f_z; (subst h_z)?, use * in auto)
        ultimately show ?thesis by auto
      qed
    next
      show "\<beta> ` {..<n + k} \<subseteq> K" unfolding \<beta>_def using Im\<alpha> \<open>\<xi> \<in> K\<close> by auto
    qed
  qed
qed

theorem analytic_factorization:
  assumes af: "f analytic_on S"
    and KS: "K \<subseteq> S"
    and con: "connected K"
    and "compact K"
    and "f not_zero_on K"
  obtains g n and \<alpha> :: "nat \<Rightarrow> complex" where
    "g analytic_on S"
    "\<And>z. z \<in> K \<Longrightarrow> g z \<noteq> 0"
    "\<And>z. z \<in> S \<Longrightarrow> f z = g z * (\<Prod>k<n. (z - \<alpha> k))"
    "\<alpha> ` {..<n} \<subseteq> K"
proof -
  have \<open>finite {z \<in> K. f z = 0}\<close> using assms by (rule analytic_compact_finite_zeros)
  moreover have \<open>finite F \<Longrightarrow> analytic_factor_p F\<close> for F
    by (induct rule: finite_induct; rule analytic_factorization_E analytic_factorization_I)
  ultimately have "analytic_factor_p {z \<in> K. f z = 0}" by auto
  hence "analytic_factor_p' f S K" unfolding analytic_factor_p_def using assms by auto
  thus ?thesis unfolding analytic_factor_p'_def using assms that by metis
qed

theorem Schwarz_Lemma1:
  fixes f :: "complex \<Rightarrow> complex"
    and \<xi> :: "complex"
  assumes "f holomorphic_on ball 0 1"
    and "f 0 = 0"
    and "\<And>z. \<parallel>z\<parallel> < 1 \<Longrightarrow> \<parallel>f z\<parallel> \<le> 1"
    and "\<parallel>\<xi>\<parallel> < 1"
  shows "\<parallel>f \<xi>\<parallel> \<le> \<parallel>\<xi>\<parallel>"
proof (cases "f constant_on ball 0 1")
  assume "f constant_on ball 0 1"
  thus ?thesis unfolding constant_on_def
    using assms by auto
next
  assume nc: "\<not>f constant_on ball 0 1"
  have "\<And>z. \<parallel>z\<parallel> < 1 \<Longrightarrow> \<parallel>f z\<parallel> < 1"
  proof -
    fix z :: complex assume *: "\<parallel>z\<parallel> < 1"
    have "\<parallel>f z\<parallel> \<noteq> 1"
    proof
      assume "\<parallel>f z\<parallel> = 1"
      hence "\<And>w. w \<in> ball 0 1 \<Longrightarrow> \<parallel>f w\<parallel> \<le> \<parallel>f z\<parallel>"
        using assms(3) by auto
      hence "f constant_on ball 0 1"
        by (intro maximum_modulus_principle [where U = "ball 0 1" and \<xi> = z])
           (use * assms(1) in auto)
      thus False using nc by blast
    qed
    with assms(3) [OF *] show "\<parallel>f z\<parallel> < 1" by auto
  qed
  thus "\<parallel>f \<xi>\<parallel> \<le> \<parallel>\<xi>\<parallel>" by (intro Schwarz_Lemma(1), use assms in auto)
qed

theorem Schwarz_Lemma2:
  fixes f :: "complex \<Rightarrow> complex"
    and \<xi> :: "complex"
  assumes holf: "f holomorphic_on ball 0 R"
    and hR: "0 < R" and nz: "f 0 = 0"
    and bn: "\<And>z. \<parallel>z\<parallel> < R \<Longrightarrow> \<parallel>f z\<parallel> \<le> 1"
    and \<xi>R: "\<parallel>\<xi>\<parallel> < R"
  shows "\<parallel>f \<xi>\<parallel> \<le> \<parallel>\<xi>\<parallel> / R"
proof -
  define \<phi> where "\<phi> z \<equiv> f (R * z)" for z :: complex
  have "\<parallel>\<xi> / R\<parallel> < 1" using \<xi>R hR by (subst nonzero_norm_divide, auto)
  moreover have "(f \<circ> (\<lambda>z. R * z)) holomorphic_on ball 0 1"
    by (rule holomorphic_on_compose, auto,
        rule holomorphic_on_subset, rule holf,
        fold scaleR_conv_of_real, use hR in auto)
  moreover have "\<phi> 0 = 0" unfolding \<phi>_def using nz by auto
  moreover have "\<And>z. \<parallel>z\<parallel> < 1 \<Longrightarrow> \<parallel>\<phi> z\<parallel> \<le> 1"
  proof -
    fix z :: complex assume *: "\<parallel>z\<parallel> < 1"
    have "\<parallel>R*z\<parallel> < R" using hR * by (fold scaleR_conv_of_real) auto
    thus "\<parallel>\<phi> z\<parallel> \<le> 1" unfolding \<phi>_def using bn by auto
  qed
  ultimately have "\<parallel>\<phi> (\<xi> / R)\<parallel> \<le> \<parallel>\<xi> / R\<parallel>"
    unfolding comp_def by (fold \<phi>_def, intro Schwarz_Lemma1)
  thus ?thesis unfolding \<phi>_def using hR by (subst (asm) nonzero_norm_divide, auto)
qed

theorem Borel_Caratheodory1:
  assumes hr: "0 < R" "0 < r" "r < R"
    and f0: "f 0 = 0"
    and hf: "\<And>z. \<parallel>z\<parallel> < R \<Longrightarrow> Re (f z) \<le> A"
    and holf: "f holomorphic_on (ball 0 R)"
    and zr: "\<parallel>z\<parallel> \<le> r"
  shows "\<parallel>f z\<parallel> \<le> 2*r/(R-r) * A"
proof -
  have A_ge_0: "A \<ge> 0"
  using f0 hf by (metis hr(1) norm_zero zero_complex.simps(1))
  then consider "A = 0" | "A > 0" by linarith
  thus "\<parallel>f z\<parallel> \<le> 2 * r/(R-r) * A"
  proof (cases)
    assume *: "A = 0"
    have 1: "\<And>w. w \<in> ball 0 R \<Longrightarrow> \<parallel>exp (f w)\<parallel> \<le> \<parallel>exp (f 0)\<parallel>" using hf f0 * by auto
    have 2: "exp \<circ> f constant_on (ball 0 R)"
      by (rule maximum_modulus_principle [where f = "exp \<circ> f" and U = "ball 0 R"])
          (use 1 hr(1) in \<open>auto intro: holomorphic_on_compose holf holomorphic_on_exp\<close>)
    have "f constant_on (ball 0 R)"
    proof (rule classical)
      assume *: "\<not> f constant_on ball 0 R"
      have "open (f ` (ball 0 R))"
        by (rule open_mapping_thm [where S = "ball 0 R"], use holf * in auto)
      then obtain e where "e > 0" and "cball 0 e \<subseteq> f ` (ball 0 R)"
        by (metis hr(1) f0 centre_in_ball imageI open_contains_cball)
      then obtain w
        where hw: "w \<in> ball 0 R" "f w = e"
        by (metis abs_of_nonneg imageE less_eq_real_def mem_cball_0 norm_of_real subset_eq)
      have "exp e = exp (f w)"
        using hw(2) by (fold exp_of_real) auto
      also have "\<dots> = exp (f 0)"
        using hw(1) 2 hr(1) unfolding constant_on_def comp_def by auto
      also have "\<dots> = exp (0 :: real)" by (subst f0) auto
      finally have "e = 0" by auto
      with \<open>e > 0\<close> show ?thesis by blast
    qed
    hence "f z = 0" using f0 hr zr unfolding constant_on_def by auto
    hence "\<parallel>f z\<parallel> = 0" by auto
    also have "\<dots> \<le> 2 * r/(R-r) * A" using hr \<open>A \<ge> 0\<close> by auto
    finally show ?thesis .
  next
    assume A_gt_0: "A > 0"
    define \<phi> where "\<phi> z \<equiv> (f z)/(2*A - f z)" for z :: complex
    have \<phi>_bound: "\<parallel>\<phi> z\<parallel> \<le> 1" if *: "\<parallel>z\<parallel> < R" for z
    proof -
      define u v where "u \<equiv> Re (f z)" and "v \<equiv> Im (f z)"
      hence "u \<le> A" unfolding u_def using hf * by blast
      hence "u\<^sup>2 \<le> (2*A-u)\<^sup>2" using A_ge_0 by (simp add: sqrt_ge_absD)
      hence "u\<^sup>2 + v\<^sup>2 \<le> (2*A-u)\<^sup>2 + (-v)\<^sup>2" by auto
      moreover have "2*A - f z = Complex (2*A-u) (-v)" by (simp add: complex_eq_iff u_def v_def)
      hence "\<parallel>f z\<parallel>\<^sup>2 = u\<^sup>2 + v\<^sup>2"
            "\<parallel>2*A - f z\<parallel>\<^sup>2 = (2*A-u)\<^sup>2 + (-v)\<^sup>2"
      unfolding u_def v_def using cmod_power2 complex.sel by presburger+
      ultimately have "\<parallel>f z\<parallel>\<^sup>2 \<le> \<parallel>2*A - f z\<parallel>\<^sup>2" by auto
      hence "\<parallel>f z\<parallel> \<le> \<parallel>2*A - f z\<parallel>" by auto
      thus ?thesis unfolding \<phi>_def by (subst norm_divide) (simp add: divide_le_eq_1)
    qed
    moreover have nz: "\<And>z :: complex. z \<in> ball 0 R \<Longrightarrow> 2*A - f z \<noteq> 0"
    proof
      fix z :: complex
      assume *: "z \<in> ball 0 R"
        and eq: "2*A - f z = 0"
      hence "Re (f z) \<le> A" using hf by auto
      moreover have "Re (f z) = 2*A"
        by (metis eq Re_complex_of_real right_minus_eq)
      ultimately show False using A_gt_0 by auto
    qed
    ultimately have "\<phi> holomorphic_on ball 0 R"
      unfolding \<phi>_def comp_def by (intro holomorphic_intros holf)
    moreover have "\<phi> 0 = 0" unfolding \<phi>_def using f0 by auto
    ultimately have *: "\<parallel>\<phi> z\<parallel> \<le> \<parallel>z\<parallel> / R"
      using hr(1) \<phi>_bound zr hr Schwarz_Lemma2 by auto
    also have "... < 1" using zr hr by auto
    finally have h\<phi>: "\<parallel>\<phi> z\<parallel> \<le> r / R" "\<parallel>\<phi> z\<parallel> < 1" "1 + \<phi> z \<noteq> 0"
    proof (safe)
      show "\<parallel>\<phi> z\<parallel> \<le> r / R" using * zr hr(1)
        by (metis divide_le_cancel dual_order.trans nle_le)
    next
      assume "1 + \<phi> z = 0"
      hence "\<phi> z = -1" using add_eq_0_iff by blast
      thus "\<parallel>\<phi> z\<parallel> < 1 \<Longrightarrow> False" by auto
    qed
    have "2*A - f z \<noteq> 0" using nz hr(3) zr by auto
    hence "f z = 2*A*\<phi> z / (1 + \<phi> z)"
      using h\<phi>(3) unfolding \<phi>_def by (auto simp add: field_simps)
    hence "\<parallel>f z\<parallel> = 2*A*\<parallel>\<phi> z\<parallel> / \<parallel>1 + \<phi> z\<parallel>"
      by (auto simp add: norm_divide norm_mult A_ge_0)
    also have "\<dots> \<le> 2*A*(\<parallel>\<phi> z\<parallel> / (1 - \<parallel>\<phi> z\<parallel>))"
    proof -
      have "\<parallel>1 + \<phi> z\<parallel> \<ge> 1 - \<parallel>\<phi> z\<parallel>"
        by (metis norm_diff_ineq norm_one)
      thus ?thesis
        by (simp, rule divide_left_mono, use A_ge_0 in auto)
           (intro mult_pos_pos, use h\<phi>(2) in auto)
    qed
    also have "\<dots> \<le> 2*A*((r/R) / (1 - r/R))"
    proof -
      have *: "a / (1 - a) \<le> b / (1 - b)"
        if "a < 1" "b < 1" "a \<le> b" for a b :: real
      using that by (auto simp add: field_simps)
      have "\<parallel>\<phi> z\<parallel> / (1 - \<parallel>\<phi> z\<parallel>) \<le> (r/R) / (1 - r/R)"
        by (rule *; (intro h\<phi>)?) (use hr in auto)
      thus ?thesis by (rule mult_left_mono, use A_ge_0 in auto)
    qed
    also have "\<dots> = 2*r/(R-r) * A" using hr(1) by (auto simp add: field_simps)
    finally show ?thesis .
  qed
qed

theorem Borel_Caratheodory2:
  assumes hr: "0 < R" "0 < r" "r < R"
    and hf: "\<And>z. \<parallel>z\<parallel> < R \<Longrightarrow> Re (f z - f 0) \<le> A"
    and holf: "f holomorphic_on (ball 0 R)"
    and zr: "\<parallel>z\<parallel> \<le> r"
  shows "\<parallel>f z - f 0\<parallel> \<le> 2*r/(R-r) * A"
proof -
  define g where "g z \<equiv> f z - f 0" for z
  show ?thesis
    by (fold g_def, rule Borel_Caratheodory1)
       (unfold g_def, insert assms, auto intro: holomorphic_intros)
qed

theorem holomorphic_on_shift [holomorphic_intros]:
  assumes "f holomorphic_on ((\<lambda>z. s + z) ` A)"
  shows "(\<lambda>z. f (s + z)) holomorphic_on A"
proof -
  have "(f \<circ> (\<lambda>z. s + z)) holomorphic_on A"
    using assms by (intro holomorphic_on_compose holomorphic_intros)
  thus ?thesis unfolding comp_def by auto
qed

theorem holomorphic_logderiv [holomorphic_intros]:
  assumes "f holomorphic_on A" "open A" "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0"
  shows "(\<lambda>s. logderiv f s) holomorphic_on A"
  using assms unfolding logderiv_def by (intro holomorphic_intros)

theorem Borel_Caratheodory3:
  assumes hr: "0 < R" "0 < r" "r < R"
    and hf: "\<And>w. w \<in> ball s R \<Longrightarrow> Re (f w - f s) \<le> A"
    and holf: "f holomorphic_on (ball s R)"
    and zr: "z \<in> ball s r"
  shows "\<parallel>f z - f s\<parallel> \<le> 2*r/(R-r) * A"
proof -
  define g where "g w \<equiv> f (s + w)" for w
  have "\<And>w. \<parallel>w\<parallel> < R \<Longrightarrow> Re (f (s + w) - f s) \<le> A"
    by (intro hf) (auto simp add: dist_complex_def)
  hence "\<parallel>g (z - s) - g 0\<parallel> \<le> 2*r/(R-r) * A"
    by (intro Borel_Caratheodory2, unfold g_def, insert assms)
       (auto intro: holomorphic_intros simp add: dist_complex_def norm_minus_commute)
  thus ?thesis unfolding g_def by auto
qed

theorem logderiv_prod:
  fixes f :: "'n \<Rightarrow> 'f \<Rightarrow> 'f :: real_normed_field"
  assumes fin: "finite I"
    and lder: "\<And>i. i \<in> I \<Longrightarrow> f i log_differentiable a"
  shows "logderiv (\<lambda>x. \<Prod>i\<in>I. f i x) a = (\<Sum>i\<in>I. logderiv (f i) a)" (is ?P)
    and "(\<lambda>x. \<Prod>i\<in>I. f i x) log_differentiable a" (is ?Q)
proof -
  let ?a = "\<lambda>i. deriv (f i) a"
  let ?b = "\<lambda>i. \<Prod>j\<in>I - {i}. f j a"
  let ?c = "\<lambda>i. f i a"
  let ?d = "\<Prod>i\<in>I. ?c i"
  have der: "\<And>i. i \<in> I \<Longrightarrow> f i field_differentiable (at a)"
    and nz: "\<And>i. i \<in> I \<Longrightarrow> f i a \<noteq> 0"
    using lder unfolding log_differentiable_def by auto
  have 1: "(*) x = (\<lambda>y. y * x)" for x :: 'f by auto
  have "((\<lambda>x. \<Prod>i\<in>I. f i x) has_derivative
    (\<lambda>y. \<Sum>i\<in>I. ?a i * y *?b i)) (at a within UNIV)"
    by (rule has_derivative_prod, fold has_field_derivative_def)
       (rule field_differentiable_derivI, elim der)
  hence 2: "DERIV (\<lambda>x. \<Prod>i\<in>I. f i x) a :> (\<Sum>i\<in>I. ?a i * ?b i)"
    unfolding has_field_derivative_def
    by (simp add: sum_distrib_left [symmetric] mult_ac)
       (subst 1, blast)
  have prod_nz: "(\<Prod>i\<in>I. ?c i) \<noteq> 0"
    using prod_zero_iff nz fin by auto
  have mult_cong: "b = c \<Longrightarrow> a * b = a * c" for a b c :: real by auto
  have "logderiv (\<lambda>x. \<Prod>i\<in>I. f i x) a = deriv (\<lambda>x. \<Prod>i\<in>I. f i x) a / ?d"
    unfolding logderiv_def by auto
  also have "\<dots> = (\<Sum>i\<in>I. ?a i * ?b i) / ?d"
    using 2 DERIV_imp_deriv by auto
  also have "\<dots> = (\<Sum>i\<in>I. ?a i * (?b i / ?d))"
    by (auto simp add: sum_divide_distrib)
  also have "\<dots> = (\<Sum>i\<in>I. logderiv (f i) a)"
  proof -
    have "\<And>a b c :: 'f. a \<noteq> 0 \<Longrightarrow> a = b * c \<Longrightarrow> c / a = inverse b"
      by (auto simp add: field_simps)
    moreover have "?d = ?c i * ?b i" if "i \<in> I" for i
      by (intro prod.remove that fin)
    ultimately have "?b i / ?d = inverse (?c i)" if "i \<in> I" for i
      using prod_nz that by auto
    thus ?thesis unfolding logderiv_def using 2
      by (auto simp add: divide_inverse intro: sum.cong)
  qed
  finally show ?P .
  show ?Q by (auto
   simp add: log_differentiable_def field_differentiable_def
     intro!: 2 prod_nz)
qed

theorem logderiv_mult:
  assumes "f log_differentiable a"
    and "g log_differentiable a"
  shows "logderiv (\<lambda>z. f z * g z) a = logderiv f a + logderiv g a" (is ?P)
    and "(\<lambda>z. f z * g z) log_differentiable a" (is ?Q)
proof -
  have "logderiv (\<lambda>z. f z * g z) a
      = logderiv (\<lambda>z. \<Prod>i\<in>{0, 1}. ([f, g]!i) z) a" by auto
  also have "\<dots> = (\<Sum>i\<in>{0, 1}. logderiv ([f, g]!i) a)"
    by (rule logderiv_prod(1), use assms in auto)
  also have "\<dots> = logderiv f a + logderiv g a"
    by auto
  finally show ?P .
  have "(\<lambda>z. \<Prod>i\<in>{0, 1}. ([f, g]!i) z) log_differentiable a"
    by (rule logderiv_prod(2), use assms in auto)
  thus ?Q by auto
qed

theorem logderiv_cong_ev:
  assumes "\<forall>\<^sub>F x in nhds x. f x = g x"
    and "x = y"
  shows "logderiv f x = logderiv g y"
proof -
  have "deriv f x = deriv g y" using assms by (rule deriv_cong_ev)
  moreover have "f x = g y" using assms by (auto intro: eventually_nhds_x_imp_x)
  ultimately show ?thesis unfolding logderiv_def by auto
qed

theorem logderiv_linear:
  assumes "z \<noteq> a"
  shows "logderiv (\<lambda>w. w - a) z = 1 / (z - a)"
    and "(\<lambda>w. w - z) log_differentiable a"
unfolding logderiv_def log_differentiable_def
  using assms by (auto simp add: derivative_intros)

theorem lemma_3_9_beta1:
  fixes f M r s\<^sub>0
  assumes zl: "0 < r" "0 \<le> M"
    and hf: "f holomorphic_on ball 0 r"
    and ne: "\<And>z. z \<in> ball 0 r \<Longrightarrow> f z \<noteq> 0"
    and bn: "\<And>z. z \<in> ball 0 r \<Longrightarrow> \<parallel>f z / f 0\<parallel> \<le> exp M"
  shows "\<parallel>logderiv f 0\<parallel> \<le> 4 * M / r"
    and "\<forall>s\<in>cball 0 (r / 4). \<parallel>logderiv f s\<parallel> \<le> 8 * M / r" 
proof (goal_cases)
  obtain g
  where holg: "g holomorphic_on ball 0 r"
    and exp_g: "\<And>x. x \<in> ball 0 r \<Longrightarrow> exp (g x) = f x"
    by (rule holomorphic_logarithm_exists [of "ball 0 r" f 0])
       (use zl(1) ne hf in auto)
  have f0: "exp (g 0) = f 0" using exp_g zl(1) by auto
  have "Re (g z - g 0) \<le> M" if *: "\<parallel>z\<parallel> < r" for z
  proof -
    have "exp (Re (g z - g 0)) = \<parallel>exp (g z - g 0)\<parallel>"
      by (rule norm_exp_eq_Re [symmetric])
    also have "\<dots> = \<parallel>f z / f 0\<parallel>"
      by (subst exp_diff, subst f0, subst exp_g)
         (use * in auto)
    also have "\<dots> \<le> exp M" by (rule bn) (use * in auto)
    finally show ?thesis by auto
  qed
  hence "\<parallel>g z - g 0\<parallel> \<le> 2 * (r / 2) / (r - r / 2) * M"
    if *: "\<parallel>z\<parallel> \<le> r / 2" for z
    by (intro Borel_Caratheodory2 [where f = g])
       (use zl(1) holg * in auto)
  also have "\<dots> = 2 * M" using zl(1) by auto
  finally have hg: "\<And>z. \<parallel>z\<parallel> \<le> r / 2 \<Longrightarrow> \<parallel>g z - g 0\<parallel> \<le> 2 * M" .
  have result: "\<parallel>logderiv f s\<parallel> \<le> 2 * M / r'"
    when "cball s r' \<subseteq> cball 0 (r / 2)" "0 < r'" "\<parallel>s\<parallel> < r / 2" for s r'
  proof -
    have contain: "\<And>z. \<parallel>s - z\<parallel> \<le> r' \<Longrightarrow> \<parallel>z\<parallel> \<le> r / 2"
      using that by (auto simp add: cball_def subset_eq dist_complex_def)
    have contain': "\<parallel>z\<parallel> < r" when "\<parallel>s - z\<parallel> \<le> r'" for z
      using zl(1) contain [of z] that by auto
    have s_in_ball: "s \<in> ball 0 r" using that(3) zl(1) by auto
    have "deriv f s = deriv (\<lambda>x. exp (g x)) s"
      by (rule deriv_cong_ev, subst eventually_nhds)
         (rule exI [where x = "ball 0 (r / 2)"], use exp_g zl(1) that(3) in auto)
    also have "\<dots> = exp (g s) * deriv g s"
      by (intro DERIV_fun_exp [THEN DERIV_imp_deriv] field_differentiable_derivI)
         (meson holg open_ball s_in_ball holomorphic_on_imp_differentiable_at)
    finally have df: "logderiv f s = deriv g s"
    proof -
      assume "deriv f s = exp (g s) * deriv g s"
      moreover have "f s \<noteq> 0" by (intro ne s_in_ball)
      ultimately show ?thesis
        unfolding logderiv_def using exp_g [OF s_in_ball] by auto
    qed
    have "\<And>z. \<parallel>s - z\<parallel> = r' \<Longrightarrow> \<parallel>g z - g 0\<parallel> \<le> 2 * M"
      using contain by (intro hg) auto
    moreover have "(\<lambda>z. g z - g 0) holomorphic_on cball s r'"
      by (rule holomorphic_on_subset [where s="ball 0 r"], insert holg)
         (auto intro: holomorphic_intros contain' simp add: dist_complex_def)
    moreover hence "continuous_on (cball s r') (\<lambda>z. g z - g 0)"
      by (rule holomorphic_on_imp_continuous_on)
    ultimately have "\<parallel>(deriv ^^ 1) (\<lambda>z. g z - g 0) s\<parallel> \<le> fact 1 * (2 * M) / r' ^ 1"
      using that(2) by (intro Cauchy_inequality) auto
    also have "\<dots> = 2 * M / r'" by auto
    also have "deriv g s = deriv (\<lambda>z. g z - g 0) s"
      by (subst deriv_diff, auto)
         (rule holomorphic_on_imp_differentiable_at, use holg s_in_ball in auto)
    hence "\<parallel>deriv g s\<parallel> = \<parallel>(deriv ^^ 1) (\<lambda>z. g z - g 0) s\<parallel>"
      by (auto simp add: derivative_intros)
    ultimately show ?thesis by (subst df) auto
  qed
  case 1 show ?case using result [of 0 "r / 2"] zl(1) by auto
  case 2 show ?case proof safe
    fix s :: complex assume hs: "s \<in> cball 0 (r / 4)"
    hence "z \<in> cball s (r / 4) \<Longrightarrow> \<parallel>z\<parallel> \<le> r / 2" for z
      using norm_triangle_sub [of "z" "s"]
      by (auto simp add: dist_complex_def norm_minus_commute)
    hence "\<parallel>logderiv f s\<parallel> \<le> 2 * M / (r / 4)"
      by (intro result) (use zl(1) hs in auto)
    also have "\<dots> = 8 * M / r" by auto
    finally show "\<parallel>logderiv f s\<parallel> \<le> 8 * M / r" .
  qed
qed

lemma deriv_shift:
  assumes "f field_differentiable at (a + x)"
  shows "deriv (\<lambda>t. f (a + t)) x = deriv f (a + x)"
proof -
  have "deriv (f \<circ> (\<lambda>t. a + t)) x = deriv f (a + x)"
    by (subst deriv_chain) (auto intro: assms)
  thus ?thesis unfolding comp_def by auto
qed

lemma logderiv_shift:
  assumes "f field_differentiable at (a + x)"
  shows "logderiv (\<lambda>t. f (a + t)) x = logderiv f (a + x)"
  unfolding logderiv_def by (subst deriv_shift) (auto intro: assms)

theorem lemma_3_9_beta1':
  fixes f M r s\<^sub>0
  assumes zl: "0 < r" "0 \<le> M"
    and hf: "f holomorphic_on ball s r"
    and ne: "\<And>z. z \<in> ball s r \<Longrightarrow> f z \<noteq> 0"
    and bn: "\<And>z. z \<in> ball s r \<Longrightarrow> \<parallel>f z / f s\<parallel> \<le> exp M"
    and hs: "z \<in> cball s (r / 4)"
  shows "\<parallel>logderiv f z\<parallel> \<le> 8 * M / r" 
proof -
  define g where "g z \<equiv> f (s + z)" for z
  have "\<forall>z \<in> cball 0 (r / 4). \<parallel>logderiv g z\<parallel> \<le> 8 * M / r"
    by (intro lemma_3_9_beta1 assms, unfold g_def)
       (auto simp add: dist_complex_def intro!: assms holomorphic_on_shift)
  note bspec [OF this, of "z - s"]
  moreover have "f field_differentiable at z"
    by (rule holomorphic_on_imp_differentiable_at [where ?s = "ball s r"])
       (insert hs zl(1), auto intro: hf simp add: dist_complex_def)
  ultimately show ?thesis unfolding g_def using hs
    by (auto simp add: dist_complex_def logderiv_shift)
qed

theorem lemma_3_9_beta2:
  fixes f M r
  assumes zl: "0 < r" "0 \<le> M"
    and af: "f analytic_on cball 0 r"
    and f0: "f 0 \<noteq> 0"
    and rz: "\<And>z. z \<in> cball 0 r \<Longrightarrow> Re z > 0 \<Longrightarrow> f z \<noteq> 0"
    and bn: "\<And>z. z \<in> cball 0 r \<Longrightarrow> \<parallel>f z / f 0\<parallel> \<le> exp M"
    and hg: "\<Gamma> \<subseteq> {z \<in> cball 0 (r / 2). f z = 0 \<and> Re z \<le> 0}"
  shows "- Re (logderiv f 0) \<le> 8 * M / r + Re (\<Sum>z\<in>\<Gamma>. 1 / z)"
proof -
  have nz': "f not_zero_on cball 0 (r / 2)"
    unfolding not_zero_on_def using f0 zl(1) by auto
  hence fin_zeros: "finite {z \<in> cball 0 (r / 2). f z = 0}"
    by (intro analytic_compact_finite_zeros [where S = "cball 0 r"])
       (use af zl in auto)
  obtain g n and \<alpha> :: "nat \<Rightarrow> complex"
  where ag: "g analytic_on cball 0 r"
    and ng: "\<And>z. z \<in> cball 0 (r / 2) \<Longrightarrow> g z \<noteq> 0"
    and fac: "\<And>z. z \<in> cball 0 r \<Longrightarrow> f z = g z * (\<Prod>k<n. (z - \<alpha> k))"
    and Im\<alpha>: "\<alpha> ` {..<n} \<subseteq> cball 0 (r / 2)"
    by (rule analytic_factorization [
      where K = "cball 0 (r / 2)"
        and S = "cball 0 r" and f = f])
       (use zl(1) af nz' in auto)
  have g0: "\<parallel>g 0\<parallel> \<noteq> 0" using ng zl(1) by auto
  hence "g holomorphic_on cball 0 r"
        "(\<lambda>z. g z / g 0) holomorphic_on cball 0 r"
    using ag by (auto simp add: analytic_intros intro: analytic_imp_holomorphic)
  hence holg:
      "g holomorphic_on ball 0 r"
      "(\<lambda>z. g z / g 0) holomorphic_on ball 0 r"
      "continuous_on (cball 0 r) (\<lambda>z. g z / g 0)"
    by (auto intro!: holomorphic_on_imp_continuous_on
                     holomorphic_on_subset [where t = "ball 0 r"])
  have nz_\<alpha>: "\<And>k. k < n \<Longrightarrow> \<alpha> k \<noteq> 0" using zl(1) f0 fac by auto
  have "\<parallel>g z / g 0\<parallel> \<le> exp M" if *: "z \<in> sphere 0 r" for z
  proof -
    let ?p = "\<parallel>(\<Prod>k<n. (z - \<alpha> k)) / (\<Prod>k<n. (0 - \<alpha> k))\<parallel>"
    have 1: "\<parallel>f z / f 0\<parallel> \<le> exp M" using bn * by auto
    have 2: "\<parallel>f z / f 0\<parallel> = \<parallel>g z / g 0\<parallel> * ?p"
      by (subst norm_mult [symmetric], subst (1 2) fac)
         (use that zl(1) in auto)
    have "?p = (\<Prod>k<n. (\<parallel>z - \<alpha> k\<parallel> / \<parallel>0 - \<alpha> k\<parallel>))"
      by (auto simp add: prod_norm [symmetric] norm_divide prod_dividef)
    also have "\<parallel>z - \<alpha> k\<parallel> \<ge> \<parallel>0 - \<alpha> k\<parallel>" if "k < n" for k
    proof (rule ccontr)
      assume **: "\<not> \<parallel>z - \<alpha> k\<parallel> \<ge> \<parallel>0 - \<alpha> k\<parallel>"
      have "r = \<parallel>z\<parallel>" using * by auto
      also have "... \<le> \<parallel>0 - \<alpha> k\<parallel> + \<parallel>z - \<alpha> k\<parallel>" by (simp add: norm_triangle_sub)
      also have "... < 2 * \<parallel>\<alpha> k\<parallel>" using ** by auto
      also have "\<alpha> k \<in> cball 0 (r / 2)" using Im\<alpha> that by blast
      hence "2 * \<parallel>\<alpha> k\<parallel> \<le> r" by auto
      finally show False by linarith
    qed
    hence "\<And>k. k < n \<Longrightarrow> \<parallel>z - \<alpha> k\<parallel> / \<parallel>0 - \<alpha> k\<parallel> \<ge> 1"
      using nz_\<alpha> by (subst le_divide_eq_1_pos) auto
    hence "(\<Prod>k<n. (\<parallel>z - \<alpha> k\<parallel> / \<parallel>0 - \<alpha> k\<parallel>)) \<ge> 1" by (rule prod_ge_1) simp
    finally have 3: "?p \<ge> 1" .
    have rule1: "b = a * c \<Longrightarrow> a \<ge> 0 \<Longrightarrow> c \<ge> 1 \<Longrightarrow> a \<le> b" for a b c :: real
      by (metis landau_omega.R_mult_left_mono more_arith_simps(6))
    have "\<parallel>g z / g 0\<parallel> \<le> \<parallel>f z / f 0\<parallel>"
      by (rule rule1) (rule 2 3 norm_ge_zero)+
    thus ?thesis using 1 by linarith
  qed
  hence "\<And>z. z \<in> cball 0 r \<Longrightarrow> \<parallel>g z / g 0\<parallel> \<le> exp M"
    by (rule_tac maximum_modulus_frontier [where f = "\<lambda>z. g z / g 0" and S = "cball 0 r"])
       (use holg in auto)
  hence bn': "\<And>z. z \<in> cball 0 (r / 2) \<Longrightarrow> \<parallel>g z / g 0\<parallel> \<le> exp M" using zl(1) by auto
  have ag': "g analytic_on cball 0 (r / 2)"
    by (rule analytic_on_subset [where S = "cball 0 r"])
       (use ag zl(1) in auto)
  have "\<parallel>logderiv g 0\<parallel> \<le> 4 * M / (r / 2)"
    by (rule lemma_3_9_beta1(1) [where f = g])
       (use zl ng bn' holg in auto)
  also have "\<dots> = 8 * M / r" by auto
  finally have bn_g: "\<parallel>logderiv g 0\<parallel> \<le> 8 * M / r" unfolding logderiv_def by auto
  let ?P = "\<lambda>w. \<Prod>k<n. (w - \<alpha> k)"
  let ?S' = "\<Sum>k<n. logderiv (\<lambda>z. z - \<alpha> k) 0"
  let ?S = "\<Sum>k<n. - (1 / \<alpha> k)"
  have "g field_differentiable at 0" using holg zl(1)
    by (auto intro!: holomorphic_on_imp_differentiable_at)
  hence ld_g: "g log_differentiable 0" unfolding log_differentiable_def using g0 by auto
  have "logderiv ?P 0 = ?S'" and ld_P: "?P log_differentiable 0"
    by (auto intro!: logderiv_linear nz_\<alpha> logderiv_prod)
  note this(1)
  also have "?S' = ?S"
    by (rule sum.cong)
       (use nz_\<alpha> in "auto cong: logderiv_linear(1)")
  finally have cd_P: "logderiv ?P 0 = ?S" .
  have "logderiv f 0 = logderiv (\<lambda>z. g z * ?P z) 0"
    by (rule logderiv_cong_ev, subst eventually_nhds)
       (intro exI [where x = "ball 0 r"], use fac zl(1) in auto)
  also have "\<dots> = logderiv g 0 + logderiv ?P 0"
    by (subst logderiv_mult) (use ld_g ld_P in auto)
  also have "\<dots> = logderiv g 0 + ?S" using cd_P by auto
  finally have "Re (logderiv f 0) = Re (logderiv g 0) + Re ?S" by simp
  moreover have "- Re (\<Sum>z\<in>\<Gamma>. 1 / z) \<le> Re ?S"
  proof -
    have "- Re (\<Sum>z\<in>\<Gamma>. 1 / z) = (\<Sum>z\<in>\<Gamma>. Re (- (1 / z)))" by (auto simp add: sum_negf)
    also have "\<dots> \<le> (\<Sum>k<n. Re (- (1 / \<alpha> k)))"
    proof (rule sum_le_included)
      show "\<forall>z\<in>\<Gamma>. \<exists>k\<in>{..<n}. \<alpha> k = z \<and> Re (- (1 / z)) \<le> Re (- (1 / \<alpha> k))"
           (is "Ball _ ?P")
      proof
        fix z assume hz: "z \<in> \<Gamma>"
        have "\<exists>k\<in>{..<n}. \<alpha> k = z"
        proof (rule ccontr, simp)
          assume ne_\<alpha>: "\<forall>k\<in>{..<n}. \<alpha> k \<noteq> z"
          have z_in: "z \<in> cball 0 (r / 2)" "z \<in> cball 0 r" using hg hz zl(1) by auto
          hence "g z \<noteq> 0" using ng by auto
          moreover have "(\<Prod>k<n. (z - \<alpha> k)) \<noteq> 0" using ne_\<alpha> hz by auto
          ultimately have "f z \<noteq> 0" using fac z_in by auto
          moreover have "f z = 0" using hz hg by auto
          ultimately show False by auto
        qed
        thus "?P z" by auto
      qed
      show "\<forall>k\<in>{..<n}. 0 \<le> Re (- (1 / \<alpha> k))" (is "Ball _ ?P")
      proof
        fix k assume *: "k\<in>{..<n}"
        have 1: "\<alpha> k \<in> cball 0 r" using Im\<alpha> zl(1) * by auto
        moreover hence "(\<Prod>j<n. (\<alpha> k - \<alpha> j)) = 0"
          by (subst prod_zero_iff) (use * in auto)
        ultimately have "f (\<alpha> k) = 0" by (subst fac) auto
        hence "Re (\<alpha> k) \<le> 0"
        proof (rule_tac ccontr)
          assume *: "f (\<alpha> k) = 0" "\<not> Re (\<alpha> k) \<le> 0"
          hence "Re (\<alpha> k) > 0" by auto
          hence "\<not> f (\<alpha> k) = 0" using rz 1 * by auto
          thus False using * by auto
        qed
        hence "Re (1 * cnj (\<alpha> k)) \<le> 0" by auto
        thus "?P k" using Re_complex_div_le_0 by auto
      qed
      show "finite {..<n}" by auto
      have "\<Gamma> \<subseteq> {z \<in> cball 0 (r / 2). f z = 0}" using hg by auto
      thus "finite \<Gamma>" using fin_zeros by (rule finite_subset)
    qed
    also have "\<dots> = Re ?S" by auto
    finally show ?thesis .
  qed
  ultimately have "- Re (logderiv f 0) - Re (\<Sum>z\<in>\<Gamma>. 1 / z) \<le> Re (- logderiv g 0)" by auto
  also have "\<dots> \<le> \<parallel>- logderiv g 0\<parallel>" by (rule complex_Re_le_cmod)
  also have "\<dots> \<le> 8 * M / r" by simp (rule bn_g)
  finally show ?thesis by auto
qed

theorem lemma_3_9_beta3:
  fixes f M r and s :: complex
  assumes zl: "0 < r" "0 \<le> M"
    and af: "f analytic_on cball s r"
    and f0: "f s \<noteq> 0"
    and rz: "\<And>z. z \<in> cball s r \<Longrightarrow> Re z > Re s \<Longrightarrow> f z \<noteq> 0"
    and bn: "\<And>z. z \<in> cball s r \<Longrightarrow> \<parallel>f z / f s\<parallel> \<le> exp M"
    and hg: "\<Gamma> \<subseteq> {z \<in> cball s (r / 2). f z = 0 \<and> Re z \<le> Re s}"
  shows "- Re (logderiv f s) \<le> 8 * M / r + Re (\<Sum>z\<in>\<Gamma>. 1 / (z - s))"
proof -
  define g where "g \<equiv> f \<circ> (\<lambda>z. s + z)"
  define \<Delta> where "\<Delta> \<equiv> (\<lambda>z. z - s) ` \<Gamma>"
  hence 1: "g analytic_on cball 0 r"
    unfolding g_def using af
    by (intro analytic_on_compose) (auto simp add: analytic_intros)
  moreover have "g 0 \<noteq> 0" unfolding g_def using f0 by auto
  moreover have "(Re z > 0 \<longrightarrow> g z \<noteq> 0) \<and> \<parallel>g z / g 0\<parallel> \<le> exp M"
    if hz: "z \<in> cball 0 r" for z
  proof (intro impI conjI)
    assume hz': "0 < Re z"
    thus "g z \<noteq> 0" unfolding g_def comp_def
      using hz by (intro rz) (auto simp add: dist_complex_def)
  next
    show "\<parallel>g z / g 0\<parallel> \<le> exp M"
      unfolding g_def comp_def using hz
      by (auto simp add: dist_complex_def intro!: bn)
  qed
  moreover have "\<Delta> \<subseteq> {z \<in> cball 0 (r / 2). g z = 0 \<and> Re z \<le> 0}"
  proof auto
    fix z assume "z \<in> \<Delta>"
    hence "s + z \<in> \<Gamma>" unfolding \<Delta>_def by auto
    thus "g z = 0" "Re z \<le> 0" "\<parallel>z\<parallel> * 2 \<le> r"
      unfolding g_def comp_def using hg by (auto simp add: dist_complex_def)
  qed
  ultimately have "- Re (logderiv g 0) \<le> 8 * M / r +  Re (\<Sum>z\<in>\<Delta>. 1 / z)"
    by (intro lemma_3_9_beta2) (use zl in auto)
  also have "\<dots> = 8 * M / r +  Re (\<Sum>z\<in>\<Gamma>. 1 / (z - s))"
    unfolding \<Delta>_def by (subst sum.reindex) (unfold inj_on_def, auto)
  finally show ?thesis
    unfolding g_def comp_def using zl(1)
    by (subst (asm) logderiv_shift)
       (auto intro: analytic_on_imp_differentiable_at [OF af])
qed

section \<open>Zero-free region of zeta funcion\<close>

lemma of_real_nat_power: "n nat_powr (of_real x :: complex) = of_real (n nat_powr x)" for n x
  by (subst of_real_of_nat_eq [symmetric])
     (subst powr_of_real, auto)

lemma norm_nat_power: "\<parallel>n nat_powr (s :: complex)\<parallel> = n powr (Re s)"
  unfolding powr_def by auto

lemma suminf_norm_bound:
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes "summable g"
    and "\<And>n. \<parallel>f n\<parallel> \<le> g n"
  shows "\<parallel>suminf f\<parallel> \<le> (\<Sum>n. g n)"
proof -
  have *: "summable (\<lambda>n. \<parallel>f n\<parallel>)"
    by (rule summable_comparison_test' [where g = g])
       (use assms in auto)
  hence "\<parallel>suminf f\<parallel> \<le> (\<Sum>n. \<parallel>f n\<parallel>)" by (rule summable_norm)
  also have "(\<Sum>n. \<parallel>f n\<parallel>) \<le> (\<Sum>n. g n)"
    by (rule suminf_le) (use assms * in auto)
  finally show ?thesis .
qed

lemma cos_inequality_1:
  fixes x :: real
  shows "3 + 4 * cos x + cos (2 * x) \<ge> 0"
proof -
  have "cos (2 * x) = (cos x)\<^sup>2 - (sin x)\<^sup>2"
    by (rule cos_double)
  also have "\<dots> = (cos x)\<^sup>2 - (1 - (cos x)\<^sup>2)"
    unfolding sin_squared_eq ..
  also have "\<dots> = 2 * (cos x)\<^sup>2 - 1" by auto
  finally have 1: "cos (2 * x) = 2 * (cos x)\<^sup>2 - 1" .
  have "0 \<le> 2 * (1 + cos x)\<^sup>2" by auto
  also have "\<dots> = 3 + 4 * cos x + (2 * (cos x)\<^sup>2 - 1)"
    by (simp add: field_simps power2_eq_square)
  finally show ?thesis unfolding 1.
qed

lemma multiplicative_fds_zeta:
  "completely_multiplicative_function (fds_nth fds_zeta_complex)"
  by standard auto

lemma fds_mangoldt_eq:
  "fds mangoldt_complex = -(fds_deriv fds_zeta / fds_zeta)"
proof -
  have "fds_nth fds_zeta_complex 1 \<noteq> 0" by auto
  hence "fds_nth (fds_deriv fds_zeta_complex / fds_zeta) n = -fds_nth fds_zeta n * mangoldt n" for n
    using multiplicative_fds_zeta
    by (intro fds_nth_logderiv_completely_multiplicative)
  thus ?thesis by (intro fds_eqI, auto)
qed

lemma abs_conv_abscissa_log_deriv:
  "abs_conv_abscissa (fds_deriv fds_zeta_complex / fds_zeta) \<le> 1"
  by (rule abs_conv_abscissa_completely_multiplicative_log_deriv
      [OF multiplicative_fds_zeta, unfolded abs_conv_abscissa_zeta], auto)

lemma abs_conv_abscissa_mangoldt:
  "abs_conv_abscissa (fds mangoldt_complex) \<le> 1"
  using abs_conv_abscissa_log_deriv
  by (subst fds_mangoldt_eq, subst abs_conv_abscissa_minus)

lemma
  assumes s: "Re s > 1"
  shows eval_fds_mangoldt: "eval_fds (fds mangoldt) s = - deriv zeta s / zeta s"
    and abs_conv_mangoldt: "fds_abs_converges (fds mangoldt) s"
proof -
  from abs_conv_abscissa_log_deriv
  have 1: "abs_conv_abscissa (fds_deriv fds_zeta_complex / fds_zeta) < ereal (s \<bullet> 1)"
    using s by (intro le_ereal_less, auto, unfold one_ereal_def, auto)
  have 2: "abs_conv_abscissa fds_zeta_complex < ereal (s \<bullet> 1)"
    using s by (subst abs_conv_abscissa_zeta, auto)
  hence 3: "fds_abs_converges (fds_deriv fds_zeta_complex / fds_zeta) s"
    by (intro fds_abs_converges) (rule 1)
  have "eval_fds (fds mangoldt) s = eval_fds (-(fds_deriv fds_zeta_complex / fds_zeta)) s"
    using fds_mangoldt_eq by auto
  also have "\<dots> = -eval_fds (fds_deriv fds_zeta_complex / fds_zeta) s"
    by (intro eval_fds_uminus fds_abs_converges_imp_converges 3)
  also have "\<dots> = -(eval_fds (fds_deriv fds_zeta_complex) s / eval_fds fds_zeta s)"
    using s by (subst eval_fds_log_deriv; ((intro 1 2)?, (auto intro!: eval_fds_zeta_nonzero)?))
  also have "\<dots> = - deriv zeta s / zeta s"
    using s by (subst eval_fds_zeta, blast, subst eval_fds_deriv_zeta, auto)
  finally show "eval_fds (fds mangoldt) s = - deriv zeta s / zeta s" .
  show "fds_abs_converges (fds mangoldt) s"
    by (subst fds_mangoldt_eq) (intro fds_abs_converges_uminus 3)
qed

lemma has_sum_summable [intro]:
  shows "(f has_sum x) A \<Longrightarrow> f summable_on A"
unfolding summable_on_def by auto

lemma sums_mangoldt:
  fixes s :: complex
  assumes s: "Re s > 1"
  shows "((\<lambda>n. mangoldt n / n nat_powr s) has_sum - deriv zeta s / zeta s) {1..}"
proof -
  let ?f = "(\<lambda>n. mangoldt n / n nat_powr s)"
  have 1: "fds_abs_converges (fds mangoldt) s"
    by (intro abs_conv_mangoldt s)
  hence 2: "fds_converges (fds mangoldt) s"
    by (rule fds_abs_converges_imp_converges)
  hence "summable (\<lambda>n. \<parallel>fds_nth (fds mangoldt) n / nat_power n s\<parallel>)"
    by (fold fds_abs_converges_def, intro 1)
  moreover have "(\<lambda>n. fds_nth (fds mangoldt) n / nat_power n s) sums (- deriv zeta s / zeta s)"
    by (subst eval_fds_mangoldt(1) [symmetric], intro s, fold fds_converges_iff, intro 2)
  ultimately have "((\<lambda>n. fds_nth (fds mangoldt) n / n nat_powr s) has_sum - deriv zeta s / zeta s) UNIV"
    by (fold nat_power_complex_def, rule norm_summable_imp_has_sum)
  moreover have [simp]: "(if n = 0 then 0 else mangoldt n) = mangoldt n" for n by auto
  ultimately have "(?f has_sum - deriv zeta s / zeta s) UNIV" by (auto simp add: fds_nth_fds)
  hence 3: "(?f has_sum - deriv zeta s / zeta s) UNIV" by auto
  have "sum ?f {0} = 0" by auto
  moreover have "(?f has_sum sum ?f {0}) {0}"
    by (rule has_sum_finite, auto)
  ultimately have "(?f has_sum 0) {0}" by auto
  hence "(?f has_sum - deriv zeta s / zeta s - 0) (UNIV - {0})"
    by (intro has_sum_Diff 3, auto)
  moreover have "UNIV - {0 :: nat} = {1..}" by auto
  ultimately show "(?f has_sum - deriv zeta s / zeta s) {1..}" by auto
qed

lemma sums_Re_logderiv_zeta:
  fixes \<sigma> t :: real
  assumes s: "\<sigma> > 1"
  shows "((\<lambda>n. mangoldt_real n * n nat_powr (-\<sigma>) * cos (t * ln n))
    has_sum Re (- deriv zeta (Complex \<sigma> t) / zeta (Complex \<sigma> t))) {1..}"
proof -
  have "Re (mangoldt n / n nat_powr (Complex \<sigma> t))
    = mangoldt_real n * n nat_powr (-\<sigma>) * cos (t * ln n)" if *: "1 \<le> n" for n
  proof -
    let ?n = "n :: complex"
    have "1 / n nat_powr (Complex \<sigma> t) = n nat_powr (Complex (-\<sigma>) (-t))"
      by (fold powr_minus_divide, auto simp add: legacy_Complex_simps)
    also have "\<dots> = exp (Complex (-\<sigma> * ln n) (-t * ln n))"
      unfolding powr_def by (auto simp add: field_simps legacy_Complex_simps, use * in linarith)
    finally have "Re (1 / n nat_powr (Complex \<sigma> t)) = Re \<dots>" by auto
    also have "\<dots> = n nat_powr (-\<sigma>) * cos (t * ln n)"
      by (unfold powr_def, subst Re_exp, use * in auto)
    finally have 1: "mangoldt_real n * Re (1 / n nat_powr (Complex \<sigma> t))
      = mangoldt_real n * n nat_powr (-\<sigma>) * cos (t * ln n)" by auto
    have rule_1: "Re (w * z) = Re w * Re z" if *: "Im w = 0" for z w :: complex using * by auto
    have "Re (mangoldt n * (1 / n nat_powr (Complex \<sigma> t)))
      = mangoldt_real n * Re (1 / n nat_powr (Complex \<sigma> t))"
      by (subst rule_1, auto)
    with 1 show ?thesis by auto
  qed
  note 1 = this
  show "((\<lambda>n. mangoldt_real n * n nat_powr (- \<sigma>) * cos (t * ln (real n)))
    has_sum Re (- deriv zeta (Complex \<sigma> t) / zeta (Complex \<sigma> t))) {1..}"
    by (subst has_sum_cong, rule 1 [symmetric],
       (auto)[1], intro has_sum_Re sums_mangoldt,
       use s in auto)
qed

lemma logderiv_zeta_ineq:
  fixes \<sigma> t :: real
  assumes s: "\<sigma> > 1"
  shows "3 * Re (logderiv zeta (Complex \<sigma> 0)) + 4 * Re (logderiv zeta (Complex \<sigma> t))
    + Re (logderiv zeta (Complex \<sigma> (2*t))) \<le> 0" (is "?x \<le> 0")
proof -
  have [simp]: "Re (-z) = - Re z" for z by auto
  have "((\<lambda>n.
      3 * (mangoldt_real n * n nat_powr (-\<sigma>) * cos (0 * ln n))
    + 4 * (mangoldt_real n * n nat_powr (-\<sigma>) * cos (t * ln n))
    + 1 * (mangoldt_real n * n nat_powr (-\<sigma>) * cos (2*t * ln n))
    ) has_sum
      3 * Re (- deriv zeta (Complex \<sigma> 0) / zeta (Complex \<sigma> 0))
    + 4 * Re (- deriv zeta (Complex \<sigma> t) / zeta (Complex \<sigma> t))
    + 1 * Re (- deriv zeta (Complex \<sigma> (2*t)) / zeta (Complex \<sigma> (2*t)))
    ) {1..}"
  by (intro has_sum_add has_sum_cmult_right sums_Re_logderiv_zeta s)
  hence *: "((\<lambda>n. mangoldt_real n * n nat_powr (-\<sigma>)
    * (3 + 4 * cos (t * ln n) + cos (2 * (t * ln n)))
    ) has_sum -?x) {1..}"
  unfolding logderiv_def by (auto simp add: field_simps)
  have "-?x \<ge> 0"
  by (rule has_sum_nonneg, rule *,
     intro mult_nonneg_nonneg,
     auto intro: mangoldt_nonneg cos_inequality_1)
  thus "?x \<le> 0" by linarith
qed

lemma sums_zeta_real:
  fixes r :: real
  assumes "1 < r"
  shows "(\<Sum>n. (n\<^sub>+) powr -r) = Re (zeta r)"
proof -
  have "(\<Sum>n. (n\<^sub>+) powr -r) = (\<Sum>n. Re (n\<^sub>+ powr (-r :: complex)))"
    by (subst of_real_nat_power) auto
  also have "\<dots> = (\<Sum>n. Re (n\<^sub>+ powr - (r :: complex)))" by auto
  also have "\<dots> = Re (\<Sum>n. n\<^sub>+ powr - (r :: complex))"
    by (intro Re_suminf [symmetric] summable_zeta)
       (use assms in auto)
  also have "\<dots> = Re (zeta r)"
    using Re_complex_of_real zeta_conv_suminf assms by presburger
  finally show ?thesis .
qed

lemma inverse_zeta_bound':
  assumes "1 < Re s"
  shows "\<parallel>inverse (zeta s)\<parallel> \<le> Re (zeta (Re s))"
proof -
  write moebius_mu (\<open>\<mu>\<close>)
  let ?f = "\<lambda>n :: nat. \<mu> (n\<^sub>+) / (n\<^sub>+) powr s"
  let ?g = "\<lambda>n :: nat. (n\<^sub>+) powr - Re s"
  have "\<parallel>\<mu> n :: complex\<parallel> \<le> 1" for n by (auto simp add: power_neg_one_If moebius_mu_def)
  hence 1: "\<parallel>?f n\<parallel> \<le> ?g n" for n
    by (auto simp add: powr_minus norm_divide norm_powr_real_powr field_simps)
  have "inverse (zeta s) = (\<Sum>n. ?f n)"
    by (intro sums_unique inverse_zeta_sums assms)
  hence "\<parallel>inverse (zeta s)\<parallel> = \<parallel>\<Sum>n. ?f n\<parallel>" by auto
  also have "\<dots> \<le> (\<Sum>n. ?g n)" by (intro suminf_norm_bound summable_zeta_real assms 1)
  finally show ?thesis using sums_zeta_real assms by auto
qed

lemma zeta_bound':
  assumes "1 < Re s"
  shows "\<parallel>zeta s\<parallel> \<le> Re (zeta (Re s))"
proof -
  let ?f = "\<lambda>n :: nat. (n\<^sub>+) powr - s"
  let ?g = "\<lambda>n :: nat. (n\<^sub>+) powr - Re s"
  have "zeta s = (\<Sum>n. ?f n)" by (intro sums_unique sums_zeta assms)
  hence "\<parallel>zeta s\<parallel> = \<parallel>\<Sum>n. ?f n\<parallel>" by auto
  also have "\<dots> \<le> (\<Sum>n. ?g n)"
    by (intro suminf_norm_bound summable_zeta_real assms)
       (subst norm_nat_power, auto)
  also have "\<dots> = Re (zeta (Re s))" by (subst sums_zeta_real) (use assms in auto)
  finally show ?thesis .
qed

lemma pre_zeta_1_bound:
  assumes "0 < Re s"
  shows "\<parallel>pre_zeta 1 s\<parallel> \<le> \<parallel>s\<parallel> / Re s"
proof -
  have "\<parallel>pre_zeta 1 s\<parallel> \<le> \<parallel>s\<parallel> / (Re s * 1 powr Re s)"
    by (rule pre_zeta_bound') (use assms in auto)
  also have "\<dots> = \<parallel>s\<parallel> / Re s" by auto
  finally show ?thesis .
qed

lemma zeta_pole_eq:
  assumes "s \<noteq> 1"
  shows "zeta s = pre_zeta 1 s + 1 / (s - 1)"
proof -
  have "zeta s - 1 / (s - 1) = pre_zeta 1 s" by (intro zeta_minus_pole_eq assms)
  thus ?thesis by (simp add: field_simps)
qed

lemma zeta_bound_trivial':
  assumes "1 / 2 \<le> Re s \<and> Re s \<le> 2"
    and "\<bar>Im s\<bar> \<ge> 1 / 11"
  shows "\<parallel>zeta s\<parallel> \<le> 15 + 2 * \<bar>Im s\<bar>"
proof -
  have "\<parallel>pre_zeta 1 s\<parallel> \<le> \<parallel>s\<parallel> / Re s"
    by (rule pre_zeta_1_bound) (use assms in auto)
  also have "\<dots> \<le> 2 * \<parallel>s\<parallel>" proof -
    have "1 \<le> Re s * 2 \<Longrightarrow> cmod s * 1 \<le> cmod s * (Re s * 2)"
      by (rule mult_left_mono) auto
    thus ?thesis using assms(1) by (auto simp add: field_simps mult_left_mono)
  qed
  also have "\<dots> \<le> 2 * (2 + \<bar>Im s\<bar>)" proof -
    have "\<parallel>s\<parallel> \<le> \<bar>Re s\<bar> + \<bar>Im s\<bar>" by (rule cmod_le)
    also have "\<dots> \<le> 2 + \<bar>Im s\<bar>" using assms(1) by auto
    finally show ?thesis by auto
  qed
  finally have 1: "\<parallel>pre_zeta 1 s\<parallel> \<le> 4 + 2 * \<bar>Im s\<bar>" by auto
  have "\<parallel>1 / (s - 1)\<parallel> = 1 / \<parallel>s - 1\<parallel>" by (subst norm_divide) auto
  also have "\<dots> \<le> 11" proof -
    have "1 / 11 \<le> \<bar>Im s\<bar>" by (rule assms(2))
    also have "\<dots> = \<bar>Im (s - 1)\<bar>" by auto
    also have "\<dots> \<le> \<parallel>s - 1\<parallel>" by (rule abs_Im_le_cmod)
    finally show ?thesis by (intro mult_imp_div_pos_le) auto
  qed
  finally have 2: "\<parallel>1 / (s - 1)\<parallel> \<le> 11" by auto
  have "zeta s = pre_zeta 1 s + 1 / (s - 1)" by (intro zeta_pole_eq) (use assms in auto)
  moreover have "\<parallel>\<dots>\<parallel> \<le> \<parallel>pre_zeta 1 s\<parallel> + \<parallel>1 / (s - 1)\<parallel>" by (rule norm_triangle_ineq)
  ultimately have "\<parallel>zeta s\<parallel> \<le> \<dots>" by auto
  also have "\<dots> \<le> 15 + 2 * \<bar>Im s\<bar>" using 1 2 by auto
  finally show ?thesis .
qed

lemma zeta_bound_gt_1:
  assumes "1 < Re s"
  shows "\<parallel>zeta s\<parallel> \<le> Re s / (Re s - 1)"
proof -
  have "\<parallel>zeta s\<parallel> \<le> Re (zeta (Re s))" by (intro zeta_bound' assms)
  also have "\<dots> \<le> \<parallel>zeta (Re s)\<parallel>" by (rule complex_Re_le_cmod)
  also have "\<dots> = \<parallel>pre_zeta 1 (Re s) + 1 / (Re s - 1)\<parallel>"
    by (subst zeta_pole_eq) (use assms in auto)
  also have "\<dots> \<le> \<parallel>pre_zeta 1 (Re s)\<parallel> + \<parallel>1 / (Re s - 1) :: complex\<parallel>"
    by (rule norm_triangle_ineq)
  also have "\<dots> \<le> 1 + 1 / (Re s - 1)"
  proof -
    have "\<parallel>pre_zeta 1 (Re s)\<parallel> \<le> \<parallel>Re s :: complex\<parallel> / Re (Re s)"
      by (rule pre_zeta_1_bound) (use assms in auto)
    also have "\<dots> = 1" using assms by auto
    moreover have "\<parallel>1 / (Re s - 1) :: complex\<parallel> = 1 / (Re s - 1)"
      by (subst norm_of_real) (use assms in auto)
    ultimately show ?thesis by auto
  qed
  also have "\<dots> = Re s / (Re s - 1)"
    using assms by (auto simp add: field_simps)
  finally show ?thesis .
qed

lemma zeta_bound_trivial:
  assumes "1 / 2 \<le> Re s" and "\<bar>Im s\<bar> \<ge> 1 / 11"
  shows "\<parallel>zeta s\<parallel> \<le> 15 + 2 * \<bar>Im s\<bar>"
proof (cases "Re s \<le> 2")
  assume "Re s \<le> 2"
  thus ?thesis by (intro zeta_bound_trivial') (use assms in auto)
next
  assume "\<not> Re s \<le> 2"
  hence *: "Re s > 1" "Re s > 2" by auto
  hence "\<parallel>zeta s\<parallel> \<le> Re s / (Re s - 1)" by (intro zeta_bound_gt_1)
  also have "\<dots> \<le> 2" using * by (auto simp add: field_simps)
  also have "\<dots> \<le> 15 + 2 * \<bar>Im s\<bar>" by auto
  finally show ?thesis .
qed

lemma zeta_nonzero_small_imag':
  assumes "\<bar>Im s\<bar> \<le> 13 / 22" and "Re s \<ge> 1 / 2" and "Re s < 1"
  shows "zeta s \<noteq> 0"
proof -
  have "\<parallel>pre_zeta 1 s\<parallel> \<le> (1 + \<parallel>s\<parallel> / Re s) / 2 * 1 powr - Re s"
    by (rule pre_zeta_bound) (use assms(2) in auto)
  also have "\<dots> \<le> 129 / 100" proof -
    have "\<parallel>s\<parallel> / Re s \<le> 79 / 50"
    proof (rule ccontr)
      assume "\<not> \<parallel>s\<parallel> / Re s \<le> 79 / 50"
      hence "sqrt (6241 / 2500) < \<parallel>s\<parallel> / Re s" by (simp add: real_sqrt_divide)
      also have "\<dots> = \<parallel>s\<parallel> / sqrt ((Re s)\<^sup>2)" using assms(2) by simp
      also have "\<dots> = sqrt (1 + (Im s / Re s)\<^sup>2)"
        unfolding cmod_def using assms(2)
        by (auto simp add: real_sqrt_divide [symmetric] field_simps
                 simp del: real_sqrt_abs)
      finally have 1: "6241 / 2500 < 1 + (Im s / Re s)\<^sup>2" by auto
      have "\<bar>Im s / Re s\<bar> \<le> \<bar>6 / 5\<bar>" using assms by (auto simp add: field_simps abs_le_square_iff)
      hence "(Im s / Re s)\<^sup>2 \<le> (6 / 5)\<^sup>2" by (subst (asm) abs_le_square_iff)
      hence 2: "1 + (Im s / Re s)\<^sup>2 \<le> 61 / 25" unfolding power2_eq_square by auto
      from 1 2 show False by auto
    qed
    hence "(1 + \<parallel>s\<parallel> / Re s) / 2 \<le> (129 / 50) / 2" by (subst divide_right_mono) auto
    also have "\<dots> = 129 / 100" by auto
    finally show ?thesis by auto
  qed
  finally have 1: "\<parallel>pre_zeta 1 s\<parallel> \<le> 129 / 100" .
  have "\<parallel>s - 1\<parallel> < 100 / 129" proof -
    from assms have "(Re (s - 1))\<^sup>2 \<le> (1 / 2)\<^sup>2" by (simp add: abs_le_square_iff [symmetric])
    moreover have "(Im (s - 1))\<^sup>2 \<le> (13 / 22)\<^sup>2" using assms(1) by (simp add: abs_le_square_iff [symmetric])
    ultimately have "(Re (s - 1))\<^sup>2 + (Im (s - 1))\<^sup>2 \<le> 145 / 242" by (auto simp add: power2_eq_square)
    hence "sqrt ((Re (s - 1))\<^sup>2 + (Im (s - 1))\<^sup>2) \<le> sqrt (145 / 242)" by (rule real_sqrt_le_mono)
    also have "\<dots> < sqrt ((100 / 129)\<^sup>2)" by (subst real_sqrt_less_iff) (simp add: power2_eq_square)
    finally show ?thesis unfolding cmod_def by auto
  qed
  moreover have "\<parallel>s - 1\<parallel> \<noteq> 0" using assms(3) by auto
  ultimately have 2: "\<parallel>1 / (s - 1)\<parallel> > 129 / 100" by (auto simp add: field_simps norm_divide)
  from 1 2 have "0 < \<parallel>1 / (s - 1)\<parallel> - \<parallel>pre_zeta 1 s\<parallel>" by auto
  also have "\<dots> \<le> \<parallel>pre_zeta 1 s + 1 / (s - 1)\<parallel>" by (subst add.commute) (rule norm_diff_ineq)
  also from assms(3) have "s \<noteq> 1" by auto
  hence "\<parallel>pre_zeta 1 s + 1 / (s - 1)\<parallel> = \<parallel>zeta s\<parallel>" using zeta_pole_eq by auto
  finally show ?thesis by auto
qed

lemma zeta_nonzero_small_imag:
  assumes "\<bar>Im s\<bar> \<le> 13 / 22" and "Re s > 0" and "s \<noteq> 1"
  shows "zeta s \<noteq> 0"
proof -
  consider "Re s \<le> 1 / 2" | "1 / 2 \<le> Re s \<and> Re s < 1" | "Re s \<ge> 1" by fastforce
  thus ?thesis proof (cases)
    case 1 hence "zeta (1 - s) \<noteq> 0" using assms by (intro zeta_nonzero_small_imag') auto
    moreover case 1
    ultimately show ?thesis using assms(2) zeta_zero_reflect_iff by auto
  next
    case 2 thus ?thesis using assms(1) by (intro zeta_nonzero_small_imag') auto
  next
    case 3 thus ?thesis using zeta_Re_ge_1_nonzero assms(3) by auto
  qed
qed

lemma inverse_zeta_bound:
  assumes "1 < Re s"
  shows "\<parallel>inverse (zeta s)\<parallel> \<le> Re s / (Re s - 1)"
proof -
  have "\<parallel>inverse (zeta s)\<parallel> \<le> Re (zeta (Re s))" by (intro inverse_zeta_bound' assms)
  also have "\<dots> \<le> \<parallel>zeta (Re s)\<parallel>" by (rule complex_Re_le_cmod)
  also have "\<dots> \<le> Re (Re s) / (Re (Re s) - 1)"
    by (intro zeta_bound_gt_1) (use assms in auto)
  also have "\<dots> = Re s / (Re s - 1)" by auto
  finally show ?thesis .
qed

lemma deriv_zeta_bound:
  fixes s :: complex
  assumes Hr: "0 < r" and Hs: "s \<noteq> 1"
    and hB: "\<And>w. \<parallel>s - w\<parallel> = r \<Longrightarrow> \<parallel>pre_zeta 1 w\<parallel> \<le> B"
  shows "\<parallel>deriv zeta s\<parallel> \<le> B / r + 1 / \<parallel>s - 1\<parallel>\<^sup>2"
proof -
  have "\<parallel>deriv zeta s\<parallel> = \<parallel>deriv (pre_zeta 1) s - 1 / (s - 1)\<^sup>2\<parallel>"
  proof -
    let ?A = "UNIV - {1 :: complex}"
    let ?f = "\<lambda>s. pre_zeta 1 s + 1 / (s - 1)"
    let ?v = "deriv (pre_zeta 1) s + (0 * (s - 1) - 1 * (1 - 0)) / (s - 1)\<^sup>2"
    let ?v' = "deriv (pre_zeta 1) s - 1 / (s - 1 :: complex)\<^sup>2"
    have "DERIV zeta s :> ?v' = DERIV ?f s :> ?v'"
      by (rule DERIV_cong_ev, auto, subst eventually_nhds)
         (rule exI [where x = ?A], insert Hs, auto intro: zeta_pole_eq)
    moreover have "DERIV ?f s :> ?v"
      unfolding power2_eq_square
      by (intro derivative_intros field_differentiable_derivI holomorphic_pre_zeta
          holomorphic_on_imp_differentiable_at [where s = ?A])
         (use Hs in auto)
    moreover have "?v = ?v'" by (auto simp add: field_simps)
    ultimately have "DERIV zeta s :> ?v'" by auto
    moreover have "DERIV zeta s :> deriv zeta s"
      by (intro field_differentiable_derivI field_differentiable_at_zeta)
         (use Hs in auto)
    ultimately have "?v' = deriv zeta s" by (rule DERIV_unique)
    thus ?thesis by auto
  qed
  also have "\<dots> \<le> \<parallel>deriv (pre_zeta 1) s\<parallel> + \<parallel>1 / (s - 1)\<^sup>2\<parallel>" by (rule norm_triangle_ineq4)
  also have "\<dots> \<le> B / r + 1 / \<parallel>s - 1\<parallel>\<^sup>2"
  proof -
    have "\<parallel>(deriv ^^ 1) (pre_zeta 1) s\<parallel> \<le> fact 1 * B / r ^ 1"
      by (intro Cauchy_inequality holomorphic_pre_zeta continuous_on_pre_zeta assms) auto
    thus ?thesis by (auto simp add: norm_divide norm_power)
  qed
  finally show ?thesis .
qed

lemma zeta_lower_bound:
  assumes "0 < Re s" "s \<noteq> 1"
  shows "1 / \<parallel>s - 1\<parallel> - \<parallel>s\<parallel> / Re s \<le> \<parallel>zeta s\<parallel>"
proof -
  have "\<parallel>pre_zeta 1 s\<parallel> \<le> \<parallel>s\<parallel> / Re s" by (intro pre_zeta_1_bound assms)
  hence "1 / \<parallel>s - 1\<parallel> - \<parallel>s\<parallel> / Re s \<le> \<parallel>1 / (s - 1)\<parallel> - \<parallel>pre_zeta 1 s\<parallel>"
    using assms by (auto simp add: norm_divide)
  also have "\<dots> \<le> \<parallel>pre_zeta 1 s + 1 / (s - 1)\<parallel>"
    by (subst add.commute) (rule norm_diff_ineq)
  also have "\<dots> = \<parallel>zeta s\<parallel>" using assms by (subst zeta_pole_eq) auto
  finally show ?thesis .
qed

lemma logderiv_zeta_bound:
  fixes \<sigma> :: real
  assumes "1 < \<sigma>" "\<sigma> \<le> 23 / 20"
  shows "\<parallel>logderiv zeta \<sigma>\<parallel> \<le> 5 / 4 * (1 / (\<sigma> - 1))"
proof -
  have "\<parallel>pre_zeta 1 s\<parallel> \<le> sqrt 2" if *: "\<parallel>\<sigma> - s\<parallel> = 1 / sqrt 2" for s :: complex
  proof -
    have 1: "0 < Re s" proof -
      have "1 - Re s \<le> Re (\<sigma> - s)" using assms(1) by auto
      also have "Re (\<sigma> - s) \<le> \<parallel>\<sigma> - s\<parallel>" by (rule complex_Re_le_cmod)
      also have "\<dots> = 1 / sqrt 2" by (rule *)
      finally have "1 - 1 / sqrt 2 \<le> Re s" by auto
      moreover have "0 < 1 - 1 / sqrt 2" by auto
      ultimately show ?thesis by linarith
    qed
    hence "\<parallel>pre_zeta 1 s\<parallel> \<le> \<parallel>s\<parallel> / Re s" by (rule pre_zeta_1_bound)
    also have "\<dots> \<le> sqrt 2" proof -
      define x y where "x \<equiv> Re s" and "y \<equiv> Im s"
      have "sqrt ((\<sigma> - x)\<^sup>2 + y\<^sup>2) = 1 / sqrt 2"
        using * unfolding cmod_def x_def y_def by auto
      also have "\<dots> = sqrt (1 / 2)" by (auto simp add: field_simps real_sqrt_mult [symmetric])
      finally have 2: "x\<^sup>2 + y\<^sup>2 - 2*\<sigma>*x + \<sigma>\<^sup>2 = 1 / 2" by (auto simp add: field_simps power2_eq_square)
      have "y\<^sup>2 \<le> x\<^sup>2" proof (rule ccontr)
        assume "\<not> y\<^sup>2 \<le> x\<^sup>2"
        hence "x\<^sup>2 < y\<^sup>2" by auto
        with 2 have "2*x\<^sup>2 - 2*\<sigma>*x + \<sigma>\<^sup>2 < 1 / 2" by auto
        hence "2 * (x - \<sigma> / 2)\<^sup>2 < (1 - \<sigma>\<^sup>2) / 2" by (auto simp add: field_simps power2_eq_square)
        also have "\<dots> < 0" using \<open>1 < \<sigma>\<close> by auto
        finally show False by auto
      qed
      moreover have "x \<noteq> 0" unfolding x_def using 1 by auto
      ultimately have "sqrt ((x\<^sup>2 + y\<^sup>2) / x\<^sup>2) \<le> sqrt 2" by (auto simp add: field_simps)
      with 1 show ?thesis unfolding cmod_def x_def y_def by (auto simp add: real_sqrt_divide)
    qed
    finally show ?thesis .
  qed
  hence "\<parallel>deriv zeta \<sigma>\<parallel> \<le> sqrt 2 / (1 / sqrt 2) + 1 / \<parallel>(\<sigma> :: complex) - 1\<parallel>\<^sup>2"
    by (intro deriv_zeta_bound) (use assms(1) in auto)
  also have "\<dots> \<le> 2 + 1 / (\<sigma> - 1)\<^sup>2"
    by (subst in_Reals_norm) (use assms(1) in auto)
  also have "\<dots> = (2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) / (\<sigma> - 1)\<^sup>2"
  proof -
    have "\<sigma> * \<sigma> - 2 * \<sigma> + 1 = (\<sigma> - 1) * (\<sigma> - 1)" by (auto simp add: field_simps)
    also have "\<dots> \<noteq> 0" using assms(1) by auto
    finally show ?thesis by (auto simp add: power2_eq_square field_simps)
  qed
  finally have 1: "\<parallel>deriv zeta \<sigma>\<parallel> \<le> (2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) / (\<sigma> - 1)\<^sup>2" .
  have "(2 - \<sigma>) / (\<sigma> - 1) = 1 / \<parallel>(\<sigma> :: complex) - 1\<parallel> - \<parallel>\<sigma> :: complex\<parallel> / Re \<sigma>"
    using assms(1) by (auto simp add: field_simps in_Reals_norm)
  also have "\<dots> \<le> \<parallel>zeta \<sigma>\<parallel>" by (rule zeta_lower_bound) (use assms(1) in auto)
  finally have 2: "(2 - \<sigma>) / (\<sigma> - 1) \<le> \<parallel>zeta \<sigma>\<parallel>" .
  have "4 * (2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) - 5 * (2 - \<sigma>) = 8 * (\<sigma> - 11 / 16)\<^sup>2 - 57 / 32"
    by (auto simp add: field_simps power2_eq_square)
  also have "\<dots> \<le> 0" proof -
    have "0 \<le> \<sigma> - 11 / 16" using assms(1) by auto
    moreover have "\<sigma> - 11 / 16 \<le> 37 / 80" using assms(2) by auto
    ultimately have "(\<sigma> - 11 / 16)\<^sup>2 \<le> (37 / 80)\<^sup>2" by auto
    thus ?thesis by (auto simp add: power2_eq_square)
  qed
  finally have "4 * (2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) - 5 * (2 - \<sigma>) \<le> 0" .
  moreover have "0 < 2 - \<sigma>" using assms(2) by auto
  ultimately have 3: "(2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) / (2 - \<sigma>) \<le> 5 / 4" by (subst pos_divide_le_eq) auto
  moreover have "0 \<le> 2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3" proof -
    have "0 \<le> 2 * (\<sigma> - 1)\<^sup>2 + 1" by auto
    also have "\<dots> = 2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3" by (auto simp add: field_simps power2_eq_square)
    finally show ?thesis .
  qed
  moreover have "0 < (2 - \<sigma>) / (\<sigma> - 1)" using assms by auto
  ultimately have "\<parallel>logderiv zeta \<sigma>\<parallel> \<le> ((2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) / (\<sigma> - 1)\<^sup>2) / ((2 - \<sigma>) / (\<sigma> - 1))"
    unfolding logderiv_def using 1 2 by (subst norm_divide) (rule frac_le, auto)
  also have "\<dots> = (2 * \<sigma>\<^sup>2 - 4 * \<sigma> + 3) / (2 - \<sigma>) * (1 / (\<sigma> - 1))"
    by (simp add: power2_eq_square)
  also have "\<dots> \<le> 5 / 4 * (1 / (\<sigma> - 1))"
    using 3 by (rule mult_right_mono) (use assms(1) in auto)
  finally show ?thesis .
qed

lemma Re_logderiv_zeta_bound:
  fixes \<sigma> :: real
  assumes "1 < \<sigma>" "\<sigma> \<le> 23 / 20"
  shows "Re (logderiv zeta \<sigma>) \<ge> - 5 / 4 * (1 / (\<sigma> - 1))"
proof -
  have "- Re (logderiv zeta \<sigma>) = Re (- logderiv zeta \<sigma>)" by auto
  also have "Re (- logderiv zeta \<sigma>) \<le> \<parallel>- logderiv zeta \<sigma>\<parallel>" by (rule complex_Re_le_cmod)
  also have "\<dots> = \<parallel>logderiv zeta \<sigma>\<parallel>" by auto
  also have "\<dots> \<le> 5 / 4 * (1 / (\<sigma> - 1))" by (intro logderiv_zeta_bound assms)
  finally show ?thesis by auto
qed

locale zeta_bound_param =
  fixes \<theta> \<phi> :: "real \<Rightarrow> real"
  assumes zeta_bn': "\<And>z. 1 - \<theta> (Im z) \<le> Re z \<Longrightarrow> Im z \<ge> 1 / 11 \<Longrightarrow> \<parallel>zeta z\<parallel> \<le> exp (\<phi> (Im z))"
    and \<theta>_pos: "\<And>t. 0 < \<theta> t \<and> \<theta> t \<le> 1 / 2"
    and \<phi>_pos: "\<And>t. 1 \<le> \<phi> t"
    and inv_\<theta>: "\<And>t. \<phi> t / \<theta> t \<le> 1 / 960 * exp (\<phi> t)"
    and mo\<theta>: "antimono \<theta>" and mo\<phi>: "mono \<phi>"
begin
  definition "region \<equiv> {z. 1 - \<theta> (Im z) \<le> Re z \<and> Im z \<ge> 1 / 11}"
  lemma zeta_bn: "\<And>z. z \<in> region \<Longrightarrow> \<parallel>zeta z\<parallel> \<le> exp (\<phi> (Im z))"
    using zeta_bn' unfolding region_def by auto
  lemma \<theta>_pos': "\<And>t. 0 < \<theta> t \<and> \<theta> t \<le> 1"
    using \<theta>_pos by (smt (verit) exp_ge_add_one_self exp_half_le2)
  lemma \<phi>_pos': "\<And>t. 0 < \<phi> t" using \<phi>_pos by (smt (verit, ccfv_SIG))
end

locale zeta_bound_param_1 = zeta_bound_param +
  fixes \<gamma> :: real
  assumes \<gamma>_cnd: "\<gamma> \<ge> 13 / 22"
begin
  definition r where "r \<equiv> \<theta> (2 * \<gamma> + 1)"
end

locale zeta_bound_param_2 = zeta_bound_param_1 +
  fixes \<sigma> \<delta> :: real
  assumes \<sigma>_cnd: "\<sigma> \<ge> 1 + exp (- \<phi>(2 * \<gamma> + 1))"
      and \<delta>_cnd: "\<delta> = \<gamma> \<or> \<delta> = 2 * \<gamma>"
begin
  definition s where "s \<equiv> Complex \<sigma> \<delta>"
end

context zeta_bound_param_2 begin
declare dist_complex_def [simp] norm_minus_commute [simp]
declare legacy_Complex_simps [simp]

lemma cball_lm:
  assumes "z \<in> cball s r"
  shows "r \<le> 1" "\<bar>Re z - \<sigma>\<bar> \<le> r" "\<bar>Im z - \<delta>\<bar> \<le> r"
        "1 / 11 \<le> Im z" "Im z \<le> 2 * \<gamma> + r"
proof -
  have "\<bar>Re (z - s)\<bar> \<le> \<parallel>z - s\<parallel>" "\<bar>Im (z - s)\<bar> \<le> \<parallel>z - s\<parallel>"
    by (rule abs_Re_le_cmod) (rule abs_Im_le_cmod)
  moreover have "\<parallel>z - s\<parallel> \<le> r" using assms by auto
  ultimately show 1: "\<bar>Re z - \<sigma>\<bar> \<le> r" "\<bar>Im z - \<delta>\<bar> \<le> r" unfolding s_def by auto
  moreover have 3: "r \<le> 1 / 2" unfolding r_def using \<theta>_pos by auto
  ultimately have 2: "\<bar>Re z - \<sigma>\<bar> \<le> 1 / 2" "\<bar>Im z - \<delta>\<bar> \<le> 1 / 2" by auto
  moreover have "\<delta> \<le> 2 * \<gamma>" using \<delta>_cnd \<gamma>_cnd by auto
  ultimately show "Im z \<le> 2 * \<gamma> + r" using 1 by auto
  have "1 / 11 \<le> \<delta> - 1 / 2" using \<delta>_cnd \<gamma>_cnd by auto
  also have "\<dots> \<le> Im z" using 2 by (auto simp del: Num.le_divide_eq_numeral1)
  finally show "1 / 11 \<le> Im z" .
  from 3 show "r \<le> 1" by auto
qed

lemma cball_in_region:
  shows "cball s r \<subseteq> region"
proof
  fix z :: complex
  assume hz: "z \<in> cball s r"
  note lm = cball_lm [OF hz]
  hence "1 - \<theta> (Im z) \<le> 1 - \<theta> (2 * \<gamma> + \<theta> (2 * \<gamma> + 1))"
    unfolding r_def using mo\<theta> lm by (auto intro: antimonoD)
  also have "\<dots> \<le> 1 + exp (-\<phi> (2 * \<gamma> + 1)) - \<theta> (2 * \<gamma> + 1)"
  proof -
    have "2 * \<gamma> + \<theta> (2 * \<gamma> + 1) \<le> 2 * \<gamma> + 1"
      unfolding r_def using \<theta>_pos' by auto
    hence "\<theta> (2 * \<gamma> + 1) - \<theta> (2 * \<gamma> + \<theta> (2 * \<gamma> + 1)) \<le> 0"
      using mo\<theta> by (auto intro: antimonoD)
    also have "0 \<le> exp (-\<phi> (2 * \<gamma> + 1))" by auto
    finally show ?thesis by auto
  qed
  also have "\<dots> \<le> \<sigma> - r" using \<sigma>_cnd unfolding r_def s_def by auto
  also have "\<dots> \<le> Re z" using lm by auto
  finally have "1 - \<theta> (Im z) \<le> Re z" .
  thus "z \<in> region" unfolding region_def using lm by auto
qed

lemma Re_s_gt_1:
  shows "1 < Re s"
proof -
  have *: "exp (- \<phi> (2 * \<gamma> + 1)) > 0" by auto
  show ?thesis using \<sigma>_cnd s_def by auto (use * in linarith)
qed

lemma zeta_analytic_on_region:
  shows "zeta analytic_on region"
  by (rule analytic_zeta) (unfold region_def, auto)

lemma exp_lemma_1:
  fixes x :: real
  assumes "1 \<le> x"
  shows "1 + exp x \<le> exp (2 * x)"
proof -
  let ?y = "exp x"
  have "ln 2 \<le> x" using assms ln_2_less_1 by auto
  hence "exp (ln 2) \<le> ?y" by (subst exp_le_cancel_iff)
  hence "(3 / 2)\<^sup>2 \<le> (?y - 1 / 2)\<^sup>2" by auto
  hence "0 \<le> - 5 / 4 + (?y - 1 / 2)\<^sup>2" by (simp add: power2_eq_square)
  also have "\<dots> = ?y\<^sup>2 - ?y - 1" by (simp add: power2_eq_square field_simps)
  finally show ?thesis by (simp add: exp_double)
qed

lemma zeta_div_bound:
  assumes "z \<in> cball s r"
  shows "\<parallel>zeta z / zeta s\<parallel> \<le> exp (3 * \<phi> (2 * \<gamma> + 1))"
proof -
  let ?\<phi> = "\<phi> (2 * \<gamma> + 1)"
  have "\<parallel>zeta z\<parallel> \<le> exp (\<phi> (Im z))" using cball_in_region zeta_bn assms by auto
  also have "\<dots> \<le> exp (?\<phi>)"
  proof -
    have "Im z \<le> 2 * \<gamma> + 1" using cball_lm [OF assms] by auto
    thus ?thesis by auto (rule monoD [OF mo\<phi>])
  qed
  also have "\<parallel>inverse (zeta s)\<parallel> \<le> exp (2 * ?\<phi>)"
  proof -
    have "\<parallel>inverse (zeta s)\<parallel> \<le> Re s / (Re s - 1)"
      by (intro inverse_zeta_bound Re_s_gt_1)
    also have "\<dots> = 1 + 1 / (Re s - 1)"
      using Re_s_gt_1 by (auto simp add: field_simps)
    also have "\<dots> \<le> 1 + exp (?\<phi>)"
    proof -
      have "Re s - 1 \<ge> exp (-?\<phi>)" using s_def \<sigma>_cnd by auto
      hence "1 / (Re s - 1) \<le> 1 / exp (-?\<phi>)"
        using Re_s_gt_1 by (auto intro: divide_left_mono)
      thus ?thesis by (auto simp add: exp_minus field_simps)
    qed
    also have "\<dots> \<le> exp (2 * ?\<phi>)" by (intro exp_lemma_1 less_imp_le \<phi>_pos)
    finally show ?thesis .
  qed
  ultimately have "\<parallel>zeta z * inverse (zeta s)\<parallel> \<le> exp (?\<phi>) * exp (2 * ?\<phi>)"
    by (subst norm_mult, intro mult_mono') auto
  also have "\<dots> = exp (3 * ?\<phi>)" by (subst exp_add [symmetric]) auto
  finally show ?thesis by (auto simp add: divide_inverse)
qed

lemma logderiv_zeta_bound:
  shows "Re (logderiv zeta s) \<ge> - 24 * \<phi> (2 * \<gamma> + 1) / r"
    and "\<And>\<beta>. \<sigma> - r / 2 \<le> \<beta> \<Longrightarrow> zeta (Complex \<beta> \<delta>) = 0 \<Longrightarrow>
        Re (logderiv zeta s) \<ge> - 24 * \<phi> (2 * \<gamma> + 1) / r + 1 / (\<sigma> - \<beta>)"
proof -
  have 1: "0 < r" unfolding r_def using \<theta>_pos' by auto
  have 2: "0 \<le> 3 * \<phi> (2 * \<gamma> + 1)" using \<phi>_pos' by (auto simp add: less_imp_le)
  have 3: "zeta s \<noteq> 0" "\<And>z. Re s < Re z \<Longrightarrow> zeta z \<noteq> 0"
    using Re_s_gt_1 by (auto intro!: zeta_Re_gt_1_nonzero)
  have 4: "zeta analytic_on cball s r" 
    by (rule analytic_on_subset;
        rule cball_in_region zeta_analytic_on_region)
  have 5: "z \<in> cball s r \<Longrightarrow> \<parallel>zeta z / zeta s\<parallel> \<le> exp (3 * \<phi> (2 * \<gamma> + 1))"
    for z by (rule zeta_div_bound)
  have 6: "{} \<subseteq> {z \<in> cball s (r / 2). zeta z = 0 \<and> Re z \<le> Re s}" by auto
  have 7: "{Complex \<beta> \<delta>} \<subseteq> {z \<in> cball s (r / 2). zeta z = 0 \<and> Re z \<le> Re s}"
    if "\<sigma> - r / 2 \<le> \<beta>" "zeta (Complex \<beta> \<delta>) = 0" for \<beta>
  proof -
    have "\<beta> \<le> \<sigma>"
      using zeta_Re_gt_1_nonzero [of "Complex \<beta> \<delta>"] Re_s_gt_1 that(2)
      unfolding s_def by fastforce
    thus ?thesis using that unfolding s_def by auto
  qed
  have "- Re (logderiv zeta s) \<le> 8 * (3 * \<phi> (2 * \<gamma> + 1)) / r + Re (\<Sum>z\<in>{}. 1 / (z - s))"
    by (intro lemma_3_9_beta3 1 2 3 4 5 6)
  thus "Re (logderiv zeta s) \<ge> - 24 * \<phi> (2 * \<gamma> + 1) / r" by auto
  show "Re (logderiv zeta s) \<ge> - 24 * \<phi> (2 * \<gamma> + 1) / r + 1 / (\<sigma> - \<beta>)"
    if *: "\<sigma> - r / 2 \<le> \<beta>" "zeta (Complex \<beta> \<delta>) = 0" for \<beta>
  proof -
    have bs: "\<beta> \<noteq> \<sigma>" using *(2) 3(1) unfolding s_def by auto
    hence bs': "1 / (\<beta> - \<sigma>) = - 1 / (\<sigma> - \<beta>)" by (auto simp add: field_simps)
    have inv_r: "1 / (Complex r 0) = Complex (1 / r) 0" if "r \<noteq> 0" for r
      using that by (auto simp add: field_simps)
    have "- Re (logderiv zeta s) \<le> 8 * (3 * \<phi> (2 * \<gamma> + 1)) / r + Re (\<Sum>z\<in>{Complex \<beta> \<delta>}. 1 / (z - s))"
      by (intro lemma_3_9_beta3 1 2 3 4 5 7 *)
    thus ?thesis unfolding s_def
      by (auto simp add: field_simps)
         (subst (asm) inv_r, use bs bs' in auto)
  qed
qed
end

context zeta_bound_param_1 begin
lemma zeta_nonzero_region':
  assumes "1 + 1 / 960 * (r / \<phi> (2 * \<gamma> + 1)) - r / 2 \<le> \<beta>"
    and "zeta (Complex \<beta> \<gamma>) = 0"
  shows "1 - \<beta> \<ge> 1 / 29760 * (r / \<phi> (2 * \<gamma> + 1))"
proof -
  let ?\<phi> = "\<phi> (2 * \<gamma> + 1)" and ?\<theta> = "\<theta> (2 * \<gamma> + 1)"
  define \<sigma> where "\<sigma> \<equiv> 1 + 1 / 960 * (r / \<phi> (2 * \<gamma> + 1))"
  define a where "a \<equiv> - 5 / 4 * (1 / (\<sigma> - 1))"
  define b where "b \<equiv> - 24 * \<phi> (2 * \<gamma> + 1) / r + 1 / (\<sigma> - \<beta>)"
  define c where "c \<equiv> - 24 * \<phi> (2 * \<gamma> + 1) / r"
  have "1 + exp (- ?\<phi>) \<le> \<sigma>"
  proof -
    have "960 * exp (- ?\<phi>) = 1 / (1 / 960 * exp ?\<phi>)"
      by (auto simp add: exp_add [symmetric] field_simps)
    also have "\<dots> \<le> 1 / (?\<phi> / ?\<theta>)" proof -
      have "?\<phi> / ?\<theta> \<le> 1 / 960 * exp ?\<phi>" by (rule inv_\<theta>)
      thus ?thesis by (intro divide_left_mono) (use \<theta>_pos \<phi>_pos' in auto)
    qed
    also have "\<dots> = r / ?\<phi>" unfolding r_def by auto
    finally show ?thesis unfolding \<sigma>_def by auto
  qed
  note * = this \<gamma>_cnd
  interpret z: zeta_bound_param_2 \<theta> \<phi> \<gamma> \<sigma> \<gamma> by (standard, use * in auto)
  interpret z': zeta_bound_param_2 \<theta> \<phi> \<gamma> \<sigma> "2 * \<gamma>" by (standard, use * in auto)
  have "r \<le> 1" unfolding r_def using \<theta>_pos' [of "2 * \<gamma> + 1"] by auto
  moreover have "1 \<le> \<phi> (2 * \<gamma> + 1)" using \<phi>_pos by auto
  ultimately have "r / \<phi> (2 * \<gamma> + 1) \<le> 1" by auto
  moreover have "0 < r" "0 < \<phi> (2 * \<gamma> + 1)" unfolding r_def using \<theta>_pos' \<phi>_pos' by auto
  hence "0 < r / \<phi> (2 * \<gamma> + 1)" by auto
  ultimately have 1: "1 < \<sigma>" "\<sigma> \<le> 23 / 20" unfolding \<sigma>_def by auto
  hence "Re (logderiv zeta \<sigma>) \<ge> a" unfolding a_def by (intro Re_logderiv_zeta_bound)
  hence "Re (logderiv zeta (Complex \<sigma> 0)) \<ge> a" by auto
  moreover have "Re (logderiv zeta z.s) \<ge> b" unfolding b_def
    by (rule z.logderiv_zeta_bound) (use assms r_def \<sigma>_def in auto)
  hence "Re (logderiv zeta (Complex \<sigma> \<gamma>)) \<ge> b" unfolding z.s_def by auto
  moreover have "Re (logderiv zeta z'.s) \<ge> c" unfolding c_def by (rule z'.logderiv_zeta_bound)
  hence "Re (logderiv zeta (Complex \<sigma> (2 * \<gamma>))) \<ge> c" unfolding z'.s_def by auto
  ultimately have "3 * a + 4 * b + c
    \<le> 3 * Re (logderiv zeta (Complex \<sigma> 0)) + 4 * Re (logderiv zeta (Complex \<sigma> \<gamma>))
    + Re (logderiv zeta (Complex \<sigma> (2 * \<gamma>)))" by auto
  also have "\<dots> \<le> 0" by (rule logderiv_zeta_ineq, rule 1)
  finally have "3 * a + 4 * b + c \<le> 0" .
  hence "4 / (\<sigma> - \<beta>) \<le> 15 / 4 * (1 / (\<sigma> - 1)) + 120 * \<phi> (2 * \<gamma> + 1) / r"
    unfolding a_def b_def c_def by auto
  also have "\<dots> = 3720 * \<phi> (2 * \<gamma> + 1) / r" unfolding \<sigma>_def by auto
  finally have 2: "inverse (\<sigma> - \<beta>) \<le> 930 * \<phi> (2 * \<gamma> + 1) / r" by (auto simp add: inverse_eq_divide)
  have 3: "\<sigma> - \<beta> \<ge> 1 / 930 * (r / \<phi> (2 * \<gamma> + 1))"
  proof -
    have "1 / 930 * (r / \<phi> (2 * \<gamma> + 1)) = 1 / (930 * (\<phi> (2 * \<gamma> + 1) / r))"
      by (auto simp add: field_simps)
    also have "\<dots> \<le> \<sigma> - \<beta>" proof -
      have "\<beta> \<le> 1" using assms(2) zeta_Re_gt_1_nonzero [of "Complex \<beta> \<gamma>"] by fastforce
      also have "1 < \<sigma>" by (rule 1)
      finally have "\<beta> < \<sigma>" .
      thus ?thesis using 2 by (rule_tac inverse_le_imp_le) auto
    qed
    finally show ?thesis .
  qed
  show ?thesis proof -
    let ?x = "r / \<phi> (2 * \<gamma> + 1)"
    have "1 / 29760 * ?x = 1 / 930 * ?x - 1 / 960 * ?x" by auto
    also have "\<dots> \<le> (\<sigma> - \<beta>) - (\<sigma> - 1)" using 3 by (subst (2) \<sigma>_def) auto
    also have "\<dots> = 1 - \<beta>" by auto
    finally show ?thesis .
  qed
qed

lemma zeta_nonzero_region:
  assumes "zeta (Complex \<beta> \<gamma>) = 0"
  shows "1 - \<beta> \<ge> 1 / 29760 * (r / \<phi> (2 * \<gamma> + 1))"
proof (cases "1 + 1 / 960 * (r / \<phi> (2 * \<gamma> + 1)) - r / 2 \<le> \<beta>")
  case True
  thus ?thesis using assms by (rule zeta_nonzero_region')
next
  case False
  let ?x = "r / \<phi> (2 * \<gamma> + 1)"
  assume 1: "\<not> 1 + 1 / 960 * ?x - r / 2 \<le> \<beta>"
  have "0 < r" using \<theta>_pos' unfolding r_def by auto
  hence "1 / 930 * ?x \<le> r / 2"
    using \<phi>_pos [of "2 * \<gamma> + 1"] by (auto intro!: mult_imp_div_pos_le)
  hence "1 / 29760 * ?x \<le> r / 2 - 1 / 960 * ?x" by auto
  also have "\<dots> \<le> 1 - \<beta>" using 1 by auto
  finally show ?thesis .
qed
end

context zeta_bound_param begin
theorem zeta_nonzero_region:
  assumes "zeta (Complex \<beta> \<gamma>) = 0" and "Complex \<beta> \<gamma> \<noteq> 1"
  shows "1 - \<beta> \<ge> 1 / 29760 * (\<theta> (2 * \<bar>\<gamma>\<bar> + 1) / \<phi> (2 * \<bar>\<gamma>\<bar> + 1))"
proof (cases "\<bar>\<gamma>\<bar> \<ge> 13 / 22")
  case True
  assume 1: "13 / 22 \<le> \<bar>\<gamma>\<bar>"
  have 2: "zeta (Complex \<beta> \<bar>\<gamma>\<bar>) = 0"
  proof (cases "\<gamma> \<ge> 0")
    case True thus ?thesis using assms by auto
  next
    case False thus ?thesis by (auto simp add: complex_cnj [symmetric] intro: assms)
  qed
  interpret z: zeta_bound_param_1 \<theta> \<phi> \<open>\<bar>\<gamma>\<bar>\<close> by standard (use 1 in auto)
  show ?thesis by (intro z.zeta_nonzero_region [unfolded z.r_def] 2)
next
  case False
  hence 1: "\<bar>\<gamma>\<bar> \<le> 13 / 22" by auto
  show ?thesis
  proof (cases "0 < \<beta>", rule ccontr)
    case True thus False using zeta_nonzero_small_imag [of "Complex \<beta> \<gamma>"] assms 1 by auto
  next
    have "0 < \<theta> (2 * \<bar>\<gamma>\<bar> + 1)" "\<theta> (2 * \<bar>\<gamma>\<bar> + 1) \<le> 1" "1 \<le> \<phi> (2 * \<bar>\<gamma>\<bar> + 1)"
      using \<theta>_pos' \<phi>_pos by auto
    hence "1 / 29760 * (\<theta> (2 * \<bar>\<gamma>\<bar> + 1) / \<phi> (2 * \<bar>\<gamma>\<bar> + 1)) \<le> 1" by auto
    also case False hence "1 \<le> 1 - \<beta>" by auto
    finally show ?thesis .
  qed
qed
end

lemma zeta_bound_param_nonneg:
  fixes \<theta> \<phi> :: "real \<Rightarrow> real"
  assumes zeta_bn': "\<And>z. 1 - \<theta> (Im z) \<le> Re z \<Longrightarrow> Im z \<ge> 1 / 11 \<Longrightarrow> \<parallel>zeta z\<parallel> \<le> exp (\<phi> (Im z))"
    and \<theta>_pos: "\<And>t. 0 \<le> t \<Longrightarrow> 0 < \<theta> t \<and> \<theta> t \<le> 1 / 2"
    and \<phi>_pos: "\<And>t. 0 \<le> t \<Longrightarrow> 1 \<le> \<phi> t"
    and inv_\<theta>: "\<And>t. 0 \<le> t \<Longrightarrow> \<phi> t / \<theta> t \<le> 1 / 960 * exp (\<phi> t)"
    and mo\<theta>: "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> \<theta> y \<le> \<theta> x"
    and mo\<phi>: "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> \<phi> x \<le> \<phi> y"
  shows "zeta_bound_param (\<lambda>t. if 0 \<le> t then \<theta> t else \<theta> 0) (\<lambda>t. if 0 \<le> t then \<phi> t else \<phi> 0)"
  by standard (insert assms, auto simp add: antimono_def mono_def)

interpretation zeta_bound_params:
  zeta_bound_param "\<lambda>t. 1 / 2" "\<lambda>t. if 0 \<le> t then 5 * ln (15 + 2 * t) else 5 * ln 15"
proof -
  define \<theta> :: "real \<Rightarrow> real" where "\<theta> \<equiv> \<lambda>t. 1 / 2"
  define \<phi> :: "real \<Rightarrow> real" where "\<phi> \<equiv> \<lambda>t. 5 * ln (15 + 2 * t)"
  have "zeta_bound_param (\<lambda>t. if 0 \<le> t then \<theta> t else \<theta> 0) (\<lambda>t. if 0 \<le> t then \<phi> t else \<phi> 0)"
  proof (rule zeta_bound_param_nonneg)
    fix z assume *: "1 - \<theta> (Im z) \<le> Re z" "Im z \<ge> 1 / 11"
    have "\<parallel>zeta z\<parallel> \<le> 15 + 2 * \<bar>Im z\<bar>"
      using * unfolding \<theta>_def by (intro zeta_bound_trivial) auto
    also have "\<dots> = exp (ln (15 + 2 * Im z))" using *(2) by auto
    also have "\<dots> \<le> exp (\<phi> (Im z))" proof -
      have "0 \<le> ln (15 + 2 * Im z)" using *(2) by auto
      thus ?thesis unfolding \<phi>_def by auto
    qed
    finally show "\<parallel>zeta z\<parallel> \<le> exp (\<phi> (Im z))" .
  next
    fix t :: real assume *: "0 \<le> t"
    have "\<phi> t / \<theta> t = 10 * ln (15 + 2 * t)" unfolding \<phi>_def \<theta>_def by auto
    also have "\<dots> \<le> 10 * (15 + 2 * t)" proof -
      have "ln (15 + 2 * t) \<le> 15 + 2 * t" by (rule ln_bound) (use * in auto)
      thus ?thesis by auto
    qed
    also have "\<dots> \<le> 1 / 960 * exp (\<phi> t)"
    proof -
      have "(9600 :: real) \<le> 15 ^ 4" by auto
      also have "\<dots> \<le> (15 + 2 * t) ^ 4" by (intro power_mono) (use * in auto)
      finally have "9600 * (15 + 2 * t) \<le> (15 + 2 * t) ^ 4 * (15 + 2 * t)"
        by (intro mult_right_mono) (use * in auto)
      also have "\<dots> = (15 + 2 * t) ^ 5" by (subst power_Suc2 [symmetric]) auto
      moreover have "exp (\<phi> t) = (15 + 2 * t) ^ 5" proof -
        have "exp (\<phi> t) = (15 + 2 * t) powr (real 5)" unfolding \<phi>_def powr_def using * by auto
        also have "\<dots> = (15 + 2 * t) ^ 5" by (rule powr_realpow) (use * in auto)
        finally show ?thesis .
      qed
      ultimately show ?thesis by auto
    qed
    finally show "\<phi> t / \<theta> t \<le> 1 / 960 * exp (\<phi> t)" .
  next
    fix t :: real assume *: "0 \<le> t"
    have "(1 :: real) \<le> 5 * 1" by auto
    also have "\<dots> \<le> 5 * ln 15" proof -
      have "exp (1 :: real) \<le> 3" by (rule exp_le)
      also have "\<dots> \<le> exp (ln 15)" by auto
      finally have "(1 :: real) \<le> ln 15" using exp_le_cancel_iff by blast
      thus ?thesis by auto
    qed
    also have "\<dots> \<le> 5 * ln (15 + 2 * t)" using * by auto
    finally show "1 \<le> \<phi> t" unfolding \<phi>_def .
  next
    show "\<And>t. 0 < \<theta> t \<and> \<theta> t \<le> 1 / 2"
         "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> \<theta> y \<le> \<theta> x"
         "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> \<phi> x \<le> \<phi> y"
      unfolding \<theta>_def \<phi>_def by auto
  qed
  thus "zeta_bound_param (\<lambda>t. 1 / 2)
    (\<lambda>t. if 0 \<le> t then 5 * ln (15 + 2 * t) else 5 * ln 15)"
    unfolding \<theta>_def \<phi>_def
    by auto (subst (asm) mult_zero_right, subst (asm) add_0_right)
qed

lemma ln_bound_1:
  fixes t :: real
  assumes Ht: "0 \<le> t"
  shows "ln (17 + 4 * t) \<le> 5 * ln (t + 2)"
proof -
  have "ln (17 + 4 * t) \<le> ln (17 / 2 * (t + 2))" using Ht by auto
  also have "\<dots> = ln (17 / 2) + ln (t + 2)" using Ht by (subst ln_mult) auto
  also have "\<dots> \<le> 4 * ln (t + 2) + ln (t + 2)" proof -
    have "(17 :: real) \<le> 2 powr 5" by auto
    hence "exp (ln (17 :: real)) \<le> exp (5 * ln 2)"
      unfolding powr_def by (subst exp_ln) auto
    hence "ln (17 :: real) \<le> 5 * ln 2" by (subst (asm) exp_le_cancel_iff)
    hence "ln (17 / 2 :: real) \<le> 4 * ln 2" by (subst ln_div) auto
    also have "\<dots> \<le> 4 * ln (t + 2)" using Ht by auto
    finally show ?thesis by auto
  qed
  also have "\<dots> = 5 * ln (t + 2)" by auto
  finally show ?thesis by (auto simp add: field_simps)
qed

definition C\<^sub>1 where "C\<^sub>1 \<equiv> (1 / 1488000 :: real)"

theorem zeta_nonzero_region:
  assumes "zeta (Complex \<beta> \<gamma>) = 0" and "Complex \<beta> \<gamma> \<noteq> 1"
  shows "1 - \<beta> \<ge> C\<^sub>1 / ln (\<bar>\<gamma>\<bar> + 2)"
proof -
  have "1 / 1488000 * (1 / ln (\<bar>\<gamma>\<bar> + 2))
      \<le> 1 / 29760 * (1 / 2 / (if 0 \<le> 2 * \<bar>\<gamma>\<bar> + 1
        then 5 * ln (15 + 2 * (2 * \<bar>\<gamma>\<bar> + 1)) else 5 * ln 15))" (is "?x \<le> ?y")
  proof -
    have "ln (17 + 4 * \<bar>\<gamma>\<bar>) \<le> 5 * ln (\<bar>\<gamma>\<bar> + 2)" by (rule ln_bound_1) auto
    hence "1 / 297600 / (5 * ln (\<bar>\<gamma>\<bar> + 2)) \<le> 1 / 297600 / (ln (17 + 4 * \<bar>\<gamma>\<bar>))"
      by (intro divide_left_mono) auto
    also have "\<dots> = ?y" by auto
    finally show ?thesis by auto
  qed
  also have "\<dots> \<le> 1 - \<beta>" by (intro zeta_bound_params.zeta_nonzero_region assms)
  finally show ?thesis unfolding C\<^sub>1_def by auto
qed

section \<open>Perron's formula\<close>

theorem powr_has_integral:
  fixes a b w :: real
  assumes Hab: "a \<le> b" and Hw: "w > 0 \<and> w \<noteq> 1"
  shows "((\<lambda>x. w powr x) has_integral w powr b / ln w - w powr a / ln w) {a..b}"
proof (rule fundamental_theorem_of_calculus)
  show "a \<le> b" using assms by auto
next
  fix x assume "x \<in> {a..b}"
  have "((\<lambda>x. exp (x * ln w)) has_vector_derivative exp (x * ln w) * (1 * ln w)) (at x within {a..b})"
    by (subst has_real_derivative_iff_has_vector_derivative [symmetric])
       (rule derivative_intros DERIV_cmult_right)+
  hence "((powr) w has_vector_derivative w powr x * ln w) (at x within {a..b})"
    unfolding powr_def using Hw by (simp add: DERIV_fun_exp)
  moreover have "ln w \<noteq> 0" using Hw by auto
  ultimately show "((\<lambda>x. w powr x / ln w) has_vector_derivative w powr x) (at x within {a..b})"
    by (auto intro: derivative_eq_intros)
qed

theorem powr_integrable:
  fixes a b w :: real
  assumes Hab: "a \<le> b" and Hw: "w > 0 \<and> w \<noteq> 1"
  shows "(\<lambda>x. w powr x) integrable_on {a..b}"
by (rule has_integral_integrable, rule powr_has_integral)
   (use assms in auto)

theorem powr_integral_bound_gt_1:
  fixes a b w :: real
  assumes Hab: "a \<le> b" and Hw: "w > 1"
  shows "integral {a..b} (\<lambda>x. w powr x) \<le> w powr b / \<bar>ln w\<bar>"
proof -
  have "integral {a..b} (\<lambda>x. w powr x) = w powr b / ln w - w powr a / ln w"
    by (intro integral_unique powr_has_integral) (use assms in auto)
  also have "\<dots> \<le> w powr b / \<bar>ln w\<bar>" using Hw by auto
  finally show ?thesis .
qed

theorem powr_integral_bound_lt_1:
  fixes a b w :: real
  assumes Hab: "a \<le> b" and Hw: "0 < w \<and> w < 1"
  shows "integral {a..b} (\<lambda>x. w powr x) \<le> w powr a / \<bar>ln w\<bar>"
proof -
  have "integral {a..b} (\<lambda>x. w powr x) = w powr b / ln w - w powr a / ln w"
    by (intro integral_unique powr_has_integral) (use assms in auto)
  also have "\<dots> \<le> w powr a / \<bar>ln w\<bar>" using Hw by (auto simp add: field_simps)
  finally show ?thesis .
qed

theorem powr_mono_lt_1_cancel:
  fixes x a b :: real
  assumes Hx: "0 < x \<and> x < 1"
  shows "(x powr a \<le> x powr b) = (b \<le> a)"
proof -
  have "(x powr a \<le> x powr b) = ((x powr -1) powr -a \<le> (x powr -1) powr -b)" by (simp add: powr_powr)
  also have "\<dots> = (-a \<le> -b)" using Hx by (intro powr_le_cancel_iff) (auto simp add: powr_neg_one)
  also have "\<dots> = (b \<le> a)" by auto
  finally show ?thesis .
qed

theorem integral_linepath_same_Re:
  assumes Ha: "Re a = Re b"
    and Hb: "Im a < Im b"
    and Hf: "(f has_contour_integral x) (linepath a b)"
  shows "((\<lambda>t. f (Complex (Re a) t) * \<i>) has_integral x) {Im a..Im b}"
proof -
  define path where "path \<equiv> linepath a b"
  define c d e g where "c \<equiv> Re a" and "d \<equiv> Im a" and "e \<equiv> Im b" and "g \<equiv> e - d"
  hence [simp]: "a = Complex c d" "b = Complex c e" by auto (subst Ha, auto)
  have hg: "0 < g" unfolding g_def using Hb by auto
  have [simp]: "a *\<^sub>R z = a * z" for a and z :: complex by (rule complex_eqI) auto
  have "((\<lambda>t. f (path t) * (b - a)) has_integral x) {0..1}"
    unfolding path_def by (subst has_contour_integral_linepath [symmetric]) (intro Hf)
  moreover have "path t = Complex c (g *\<^sub>R t + d)" for t
    unfolding path_def linepath_def g_def
    by (auto simp add: field_simps legacy_Complex_simps)
  moreover have "b - a = g * \<i>"
    unfolding g_def by (auto simp add: legacy_Complex_simps)
  ultimately have
    "((\<lambda>t. f (Complex c (g *\<^sub>R t + d)) * (g * \<i>)) has_integral g * x /\<^sub>R g ^ DIM(real))
     (cbox ((d - d) /\<^sub>R g) ((e - d) /\<^sub>R g))"
    by (subst (6) g_def) (auto simp add: field_simps)
  hence "((\<lambda>t. f (Complex c t) * \<i> * g) has_integral x * g) {d..e}"
    by (subst (asm) has_integral_affinity_iff)
       (auto simp add: field_simps hg)
  hence "((\<lambda>t. f (Complex c t) * \<i> * g * (1 / g)) has_integral x * g * (1 / g)) {d..e}"
    by (rule has_integral_mult_left)
  thus ?thesis using hg by auto
qed

theorem perron_aux_3':
  fixes f :: "complex \<Rightarrow> complex" and a b B T :: real
  assumes Ha: "0 < a" and Hb: "0 < b" and hT: "0 < T"
    and Hf: "\<And>t. t \<in> {-T..T} \<Longrightarrow> \<parallel>f (Complex b t)\<parallel> \<le> B"
    and Hf': "(\<lambda>s. f s * a powr s / s) contour_integrable_on (linepath (Complex b (-T)) (Complex b T))"
  shows "\<parallel>1 / (2 * pi * \<i>) * contour_integral (linepath (Complex b (-T)) (Complex b T)) (\<lambda>s. f s * a powr s / s)\<parallel>
       \<le> B * a powr b * ln (1 + T / b)"
proof -
  define path where "path \<equiv> linepath (Complex b (-T)) (Complex b T)"
  define t' where "t' t \<equiv> Complex (Re (Complex b (-T))) t" for t
  define g where "g t \<equiv> f (Complex b t) * a powr (Complex b t) / Complex b t * \<i>" for t
  have hB: "0 \<le> B" using Hf [of 0] hT by (auto, smt (verit) norm_ge_zero)
  have "((\<lambda>t. f (t' t) * a powr (t' t) / (t' t) * \<i>)
        has_integral contour_integral path (\<lambda>s. f s * a powr s / s)) {Im (Complex b (-T))..Im (Complex b T)}"
    unfolding t'_def using hT
    by (intro integral_linepath_same_Re, unfold path_def)
       (auto intro: has_contour_integral_integral Hf')
  hence h_int: "(g has_integral contour_integral path (\<lambda>s. f s * a powr s / s)) {-T..T}"
    unfolding g_def t'_def by auto
  hence int: "g integrable_on {-T..T}" by (rule has_integral_integrable)
  have "contour_integral path (\<lambda>s. f s * a powr s / s) = integral {-T..T} g"
    using h_int by (rule integral_unique [symmetric])
  also have "\<parallel>\<dots>\<parallel> \<le> integral {-T..T} (\<lambda>t. 2 * B * a powr b / (b + \<bar>t\<bar>))"
  proof (rule integral_norm_bound_integral, goal_cases)
    case 1 from int show ?case .
    case 2 show ?case
      by (intro integrable_continuous_interval continuous_intros)
         (use Hb in auto)
  next
    fix t assume *: "t \<in> {-T..T}"
    have "(b + \<bar>t\<bar>)\<^sup>2 - 4 * (b\<^sup>2 + t\<^sup>2) = - 3 * (b - \<bar>t\<bar>)\<^sup>2 + - 4 * b * \<bar>t\<bar>"
      by (simp add: field_simps power2_eq_square)
    also have "\<dots> \<le> 0" using Hb by (intro add_nonpos_nonpos) auto
    finally have "(b + \<bar>t\<bar>)\<^sup>2 - 4 * (b\<^sup>2 + t\<^sup>2) \<le> 0" .
    hence "b + \<bar>t\<bar> \<le> 2 * \<parallel>Complex b t\<parallel>"
      unfolding cmod_def by (rule_tac power2_le_imp_le) auto
    hence "a powr b / \<parallel>Complex b t\<parallel> \<le> a powr b / ((b + \<bar>t\<bar>) / 2)"
      using Hb by (intro divide_left_mono) (auto intro!: mult_pos_pos)
    hence "a powr b / \<parallel>Complex b t\<parallel> * \<parallel>f (Complex b t)\<parallel> \<le> a powr b / ((b + \<bar>t\<bar>) / 2) * B"
      by (insert Hf [OF *], rule mult_mono) (use Hb in auto)
    thus "\<parallel>g t\<parallel> \<le> 2 * B * a powr b / (b + \<bar>t\<bar>)"
      unfolding g_def
      by (auto simp add: norm_mult norm_divide)
         (subst norm_powr_real_powr, insert Ha, auto simp add: mult_ac)
  qed
  also have "\<dots> = 2 * B * a powr b * integral {-T..T} (\<lambda>t. 1 / (b + \<bar>t\<bar>))"
    by (subst divide_inverse, subst integral_mult_right) (simp add: inverse_eq_divide)
  also have "\<dots> = 4 * B * a powr b * integral {0..T} (\<lambda>t. 1 / (b + \<bar>t\<bar>))"
  proof -
    let ?f = "\<lambda>t. 1 / (b + \<bar>t\<bar>)"
    have "integral {-T..0} ?f + integral {0..T} ?f = integral {-T..T} ?f"
      by (intro integral_combine integrable_continuous_interval continuous_intros)
         (use Hb hT in auto)
    moreover have "integral {-T..-0} (\<lambda>t. ?f (-t)) = integral {0..T} ?f" by (rule integral_reflect_real)
    hence "integral {-T..0} ?f = integral {0..T} ?f" by auto
    ultimately show ?thesis by auto
  qed
  also have "\<dots> = 4 * B * a powr b * ln (1 + T / b)"
  proof -
    have "((\<lambda>t. 1 / (b + \<bar>t\<bar>)) has_integral (ln (b + T) - ln (b + 0))) {0..T}"
    proof (rule fundamental_theorem_of_calculus, goal_cases)
      case 1 show ?case using hT by auto
    next
      fix x assume *: "x \<in> {0..T}"
      have "((\<lambda>x. ln (b + x)) has_real_derivative 1 / (b + x) * (0 + 1)) (at x within {0..T})"
        by (intro derivative_intros) (use Hb * in auto)
      thus "((\<lambda>x. ln (b + x)) has_vector_derivative 1 / (b + \<bar>x\<bar>)) (at x within {0..T})"
        using * by (subst has_real_derivative_iff_has_vector_derivative [symmetric]) auto
    qed
    moreover have "ln (b + T) - ln (b + 0) = ln (1 + T / b)"
      using Hb hT by (subst ln_div [symmetric]) (auto simp add: field_simps)
    ultimately show ?thesis by auto
  qed
  finally have "\<parallel>1 / (2 * pi * \<i>) * contour_integral path (\<lambda>s. f s * a powr s / s)\<parallel>
    \<le> 1 / (2*pi) * 4 * B * a powr b * ln (1 + T / b)"
    by (simp add: norm_divide norm_mult field_simps)
  also have "\<dots> \<le> 1 * B * a powr b * ln (1 + T / b)"
  proof -
    have "1 / (2*pi) * 4 \<le> 1" using pi_gt3 by auto
    thus ?thesis by (intro mult_right_mono) (use hT Hb hB in auto)
  qed
  finally show ?thesis unfolding path_def by auto
qed

definition has_subsum where "has_subsum f S x \<equiv> (\<lambda>n. if n \<in> S then f n else 0) sums x"
definition subsum where "subsum f S \<equiv> \<Sum>n. if n \<in> S then f n else 0"
definition subsummable (infix "subsummable" 50)
  where "f subsummable S \<equiv> summable (\<lambda>n. if n \<in> S then f n else 0)"

syntax "_subsum" :: "pttrn \<Rightarrow> nat set \<Rightarrow> 'a \<Rightarrow> 'a"
  ("(2\<Sum>`_ \<in> (_)./ _)" [0, 0, 10] 10)
translations
  "\<Sum>` x\<in>S. t" => "CONST subsum (\<lambda>x. t) S"

syntax "_subsum_prop" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"
  ("(2\<Sum>`_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Sum>` x|P. t" => "CONST subsum (\<lambda>x. t) {x. P}"

syntax "_subsum_ge" :: "pttrn \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"
  ("(2\<Sum>`_ \<ge> _./ _)" [0, 0, 10] 10)
translations
  "\<Sum>` x\<ge>n. t" => "CONST subsum (\<lambda>x. t) {n..}"

theorem has_subsum_finite:
  "finite F \<Longrightarrow> has_subsum f F (sum f F)"
  unfolding has_subsum_def by (rule sums_If_finite_set)

theorem has_subsum_If_finite_set:
  assumes "finite F"
  shows "has_subsum (\<lambda>n. if n \<in> F then f n else 0) A (sum f (F \<inter> A))"
proof -
  have "F \<inter> A = {x. x \<in> A \<and> x \<in> F}" by auto
  thus ?thesis unfolding has_subsum_def using assms
    by (auto simp add: if_if_eq_conj intro!: sums_If_finite)
qed

theorem has_subsum_If_finite:
  assumes "finite {n \<in> A. p n}"
  shows "has_subsum (\<lambda>n. if p n then f n else 0) A (sum f {n \<in> A. p n})"
unfolding has_subsum_def using assms
  by (auto simp add: if_if_eq_conj intro!: sums_If_finite)

theorem has_subsum_univ:
  "f sums v \<Longrightarrow> has_subsum f UNIV v" 
  unfolding has_subsum_def by auto

theorem subsumI:
  fixes f :: "nat \<Rightarrow> 'a :: {t2_space, comm_monoid_add}"
  shows "has_subsum f A x \<Longrightarrow> x = subsum f A"
  unfolding has_subsum_def subsum_def by (intro sums_unique)

theorem has_subsum_summable:
  "has_subsum f A x \<Longrightarrow> f subsummable A"
  unfolding has_subsum_def subsummable_def by (rule sums_summable)

theorem subsummable_sums:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_monoid_add, t2_space}"
  shows "f subsummable S \<Longrightarrow> has_subsum f S (subsum f S)"
  unfolding subsummable_def has_subsum_def subsum_def by (intro summable_sums)

theorem has_subsum_diff_finite:
  fixes S :: "'a :: {topological_ab_group_add, t2_space}"
  assumes "finite F" "has_subsum f A S" "F \<subseteq> A"
  shows "has_subsum f (A - F) (S - sum f F)"
proof -
  define p where "p n \<equiv> if n \<in> F then 0 else (if n \<in> A then f n else 0)" for n
  define q where "q n \<equiv> if n \<in> A - F then f n else 0" for n
  have "F \<inter> A = F" using assms(3) by auto
  hence "p sums (S - sum f F)"
    using assms unfolding p_def has_subsum_def
    by (rule_tac sums_If_finite_set' [where ?S = S])
       (auto simp add: sum_negf sum.inter_restrict [symmetric])
  moreover have "p = q" unfolding p_def q_def by auto
  finally show ?thesis unfolding q_def has_subsum_def by auto
qed

theorem subsum_split:
  fixes f :: "nat \<Rightarrow> 'a :: {topological_ab_group_add, t2_space}"
  assumes "f subsummable A" "finite F" "F \<subseteq> A"
  shows "subsum f A = sum f F + subsum f (A - F)"
proof -
  from assms(1) have "has_subsum f A (subsum f A)" by (intro subsummable_sums)
  hence "has_subsum f (A - F) (subsum f A - sum f F)"
    using assms by (intro has_subsum_diff_finite)
  hence "subsum f A - sum f F = subsum f (A - F)" by (rule subsumI)
  thus ?thesis by (auto simp add: algebra_simps)
qed

theorem has_subsum_zero [simp]: "has_subsum (\<lambda>n. 0) A 0" unfolding has_subsum_def by auto
theorem zero_subsummable [simp]: "(\<lambda>n. 0) subsummable A" unfolding subsummable_def by auto
theorem zero_subsum [simp]: "(\<Sum>`n\<in>A. 0 :: 'a :: {comm_monoid_add, t2_space}) = 0" unfolding subsum_def by auto

theorem has_subsum_minus:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_vector"
  assumes "has_subsum f A a" "has_subsum g A b"
  shows "has_subsum (\<lambda>n. f n - g n) A (a - b)"
proof -
  define p where "p n = (if n \<in> A then f n else 0)" for n
  define q where "q n = (if n \<in> A then g n else 0)" for n
  have "(\<lambda>n. p n - q n) sums (a - b)"
    using assms unfolding p_def q_def has_subsum_def by (intro sums_diff)
  moreover have "(if n \<in> A then f n - g n else 0) = p n - q n" for n
    unfolding p_def q_def by auto
  ultimately show ?thesis unfolding has_subsum_def by auto
qed

theorem subsum_minus:
  assumes "f subsummable A" "g subsummable A"
  shows "subsum f A - subsum g A = (\<Sum>`n\<in>A. f n - g n :: 'a :: real_normed_vector)"
  by (intro subsumI has_subsum_minus subsummable_sums assms)

theorem subsummable_minus:
  assumes "f subsummable A" "g subsummable A"
  shows "(\<lambda>n. f n - g n :: 'a :: real_normed_vector) subsummable A"
  by (auto intro: has_subsum_summable has_subsum_minus subsummable_sums assms)

theorem has_subsum_uminus:
  assumes "has_subsum f A a"
  shows "has_subsum (\<lambda>n. - f n :: 'a :: real_normed_vector) A (- a)"
proof -
  have "has_subsum (\<lambda>n. 0 - f n) A (0 - a)"
    by (intro has_subsum_minus) (use assms in auto)
  thus ?thesis by auto
qed

theorem subsum_uminus:
  "f subsummable A \<Longrightarrow> - subsum f A = (\<Sum>`n\<in>A. - f n :: 'a :: real_normed_vector)"
  by (intro subsumI has_subsum_uminus subsummable_sums)

theorem subsummable_uminus:
  "f subsummable A \<Longrightarrow> (\<lambda>n. - f n :: 'a :: real_normed_vector) subsummable A"
  by (auto intro: has_subsum_summable has_subsum_uminus subsummable_sums)

theorem has_subsum_add:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_vector"
  assumes "has_subsum f A a" "has_subsum g A b"
  shows "has_subsum (\<lambda>n. f n + g n) A (a + b)"
proof -
  have "has_subsum (\<lambda>n. f n - - g n) A (a - - b)"
    by (intro has_subsum_minus has_subsum_uminus assms)
  thus ?thesis by auto
qed

theorem subsum_add:
  assumes "f subsummable A" "g subsummable A"
  shows "subsum f A + subsum g A = (\<Sum>`n\<in>A. f n + g n :: 'a :: real_normed_vector)"
  by (intro subsumI has_subsum_add subsummable_sums assms)

theorem subsummable_add:
  assumes "f subsummable A" "g subsummable A"
  shows "(\<lambda>n. f n + g n :: 'a :: real_normed_vector) subsummable A"
  by (auto intro: has_subsum_summable has_subsum_add subsummable_sums assms)

theorem subsum_cong:
  "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> subsum f A = subsum g A"
  unfolding subsum_def by (intro suminf_cong) auto

theorem subsummable_cong:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_vector"
  shows "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> (f subsummable A) = (g subsummable A)"
  unfolding subsummable_def by (intro summable_cong) auto

theorem subsum_norm_bound:
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes "g subsummable A" "\<And>n. n \<in> A \<Longrightarrow> \<parallel>f n\<parallel> \<le> g n"
  shows "\<parallel>subsum f A\<parallel> \<le> subsum g A"
  using assms unfolding subsummable_def subsum_def
  by (intro suminf_norm_bound) auto

theorem eval_fds_subsum:
  fixes f :: "'a :: {nat_power, banach, real_normed_field} fds"
  assumes "fds_converges f s"
  shows "has_subsum (\<lambda>n. fds_nth f n / nat_power n s) {1..} (eval_fds f s)"
proof -
  let ?f = "\<lambda>n. fds_nth f n / nat_power n s"
  let ?v = "eval_fds f s"
  have "has_subsum (\<lambda>n. ?f n) UNIV ?v"
    by (intro has_subsum_univ fds_converges_iff [THEN iffD1] assms)
  hence "has_subsum ?f (UNIV - {0}) (?v - sum ?f {0})"
    by (intro has_subsum_diff_finite) auto
  moreover have "UNIV - {0 :: nat} = {1..}" by auto
  ultimately show ?thesis by auto
qed

theorem fds_abs_subsummable:
  fixes f :: "'a :: {nat_power, banach, real_normed_field} fds"
  assumes "fds_abs_converges f s"
  shows "(\<lambda>n. \<parallel>fds_nth f n / nat_power n s\<parallel>) subsummable {1..}"
proof -
  have "summable (\<lambda>n. \<parallel>fds_nth f n / nat_power n s\<parallel>)"
    by (subst fds_abs_converges_def [symmetric]) (rule assms)
  moreover have "\<parallel>fds_nth f n / nat_power n s\<parallel> = 0" when "\<not> 1 \<le> n" for n
  proof -
    have "n = 0" using that by auto
    thus ?thesis by auto
  qed
  hence "(\<lambda>n. if 1 \<le> n then \<parallel>fds_nth f n / nat_power n s\<parallel> else 0)
       = (\<lambda>n. \<parallel>fds_nth f n / nat_power n s\<parallel>)" by auto
  ultimately show ?thesis unfolding subsummable_def by auto
qed

theorem subsum_mult2:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_algebra"
  shows "f subsummable A \<Longrightarrow> (\<Sum>`x\<in>A. f x * c) = subsum f A * c"
unfolding subsum_def subsummable_def
  by (subst suminf_mult2) (auto intro: suminf_cong)

theorem subsummable_mult2:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_algebra"
  assumes "f subsummable A"
  shows "(\<lambda>x. f x * c) subsummable A"
proof -
  have "summable (\<lambda>n. (if n \<in> A then f n else 0) * c)" (is ?P)
    using assms unfolding subsummable_def by (intro summable_mult2)
  moreover have "?P = ?thesis"
    unfolding subsummable_def by (rule summable_cong) auto
  ultimately show ?thesis by auto
qed

theorem subsum_ge_limit:
  "lim (\<lambda>N. \<Sum>n = m..N. f n) = (\<Sum>`n \<ge> m. f n)"
proof -
  define g where "g n \<equiv> if n \<in> {m..} then f n else 0" for n
  have "(\<Sum>n. g n) = lim (\<lambda>N. \<Sum>n<N. g n)" by (rule suminf_eq_lim)
  also have "\<dots> = lim (\<lambda>N. \<Sum>n<N + 1. g n)"
    unfolding lim_def using LIMSEQ_ignore_initial_segment LIMSEQ_offset
    by (intro The_cong iffI) blast
  also have "\<dots> = lim (\<lambda>N. \<Sum>n = m..N. f n)"
  proof -
    have "{x. x < N + 1 \<and> m \<le> x} = {m..N}" for N by auto
    thus ?thesis unfolding g_def by (subst sum.inter_filter [symmetric]) auto
  qed
  finally show ?thesis unfolding subsum_def g_def by auto
qed

theorem has_subsum_ge_limit:
  fixes f :: "nat \<Rightarrow> 'a :: {t2_space, comm_monoid_add, topological_space}"
  assumes "((\<lambda>N. \<Sum>n = m..N. f n) \<longlongrightarrow> l) at_top"
  shows "has_subsum f {m..} l"
proof -
  define g where "g n \<equiv> if n \<in> {m..} then f n else 0" for n
  have "((\<lambda>N. \<Sum>n<N + 1. g n) \<longlongrightarrow> l) at_top"
  proof -
    have "{x. x < N + 1 \<and> m \<le> x} = {m..N}" for N by auto
    with assms show ?thesis
      unfolding g_def by (subst sum.inter_filter [symmetric]) auto
  qed
  hence "((\<lambda>N. \<Sum>n<N. g n) \<longlongrightarrow> l) at_top" by (rule_tac LIMSEQ_offset)
  thus ?thesis unfolding has_subsum_def sums_def g_def by auto
qed

theorem eval_fds_complex:
  fixes f :: "complex fds"
  assumes "fds_converges f s"
  shows "has_subsum (\<lambda>n. fds_nth f n / n nat_powr s) {1..} (eval_fds f s)"
proof -
  have "has_subsum (\<lambda>n. fds_nth f n / nat_power n s) {1..} (eval_fds f s)"
    by (intro eval_fds_subsum assms)
  thus ?thesis unfolding nat_power_complex_def .
qed

theorem eval_fds_complex_subsum:
  fixes f :: "complex fds"
  assumes "fds_converges f s"
  shows "eval_fds f s = (\<Sum>`n \<ge> 1. fds_nth f n / n nat_powr s)"
        "(\<lambda>n. fds_nth f n / n nat_powr s) subsummable {1..}"
proof (goal_cases)
  case 1 show ?case by (intro subsumI eval_fds_complex assms)
  case 2 show ?case by (intro has_subsum_summable) (rule eval_fds_complex assms)+
qed

theorem nat_lt_real_iff:
  "(n :: nat) < (a :: real) = (n < nat \<lceil>a\<rceil>)"
proof -
  have "n < a = (of_int n < a)" by auto
  also have "\<dots> = (n < \<lceil>a\<rceil>)" by (rule less_ceiling_iff [symmetric])
  also have "\<dots> = (n < nat \<lceil>a\<rceil>)" by auto
  finally show ?thesis .
qed

theorem nat_le_real_iff:
  "(n :: nat) \<le> (a :: real) = (n < nat (\<lfloor>a\<rfloor> + 1))"
proof -
  have "n \<le> a = (of_int n \<le> a)" by auto
  also have "\<dots> = (n \<le> \<lfloor>a\<rfloor>)" by (rule le_floor_iff [symmetric])
  also have "\<dots> = (n < \<lfloor>a\<rfloor> + 1)" by auto
  also have "\<dots> = (n < nat (\<lfloor>a\<rfloor> + 1))" by auto
  finally show ?thesis .
qed

locale perron_locale =
  fixes b B H T x :: real and f :: "complex fds"
  assumes Hb: "0 < b" and hT: "b \<le> T"
    and Hb': "abs_conv_abscissa f < b"
    and hH: "2 \<le> H" and hH': "b + 1 \<le> H" and Hx: "2 \<le> x"
    and hB: "(\<Sum>`n \<ge> 1. \<parallel>fds_nth f n\<parallel> / n nat_powr b) \<le> B"
begin
definition r where "r a \<equiv>
  if a \<noteq> 1 then min (1 / (2 * T * \<bar>ln a\<bar>)) (2 + ln (T / b))
  else (2 + ln (T / b))"
definition path where "path \<equiv> linepath (Complex b (-T)) (Complex b T)"
definition img_path where "img_path \<equiv> path_image path"
definition \<sigma>\<^sub>a where "\<sigma>\<^sub>a \<equiv> abs_conv_abscissa f"
definition region where "region = {n :: nat. x - x / H \<le> n \<and> n \<le> x + x / H}"
definition F where "F (a :: real) \<equiv>
  1 / (2 * pi * \<i>) * contour_integral path (\<lambda>s. a powr s / s) - (if 1 \<le> a then 1 else 0)"
definition F' where "F' (n :: nat) \<equiv> F (x / n)"

lemma hT': "0 < T" using Hb hT by auto
lemma cond: "0 < b" "b \<le> T" "0 < T" using Hb hT hT' by auto

theorem perron_integrable:
  assumes "(0 :: real) < a"
  shows "(\<lambda>s. a powr s / s) contour_integrable_on (linepath (Complex b (-T)) (Complex b T))"
using cond assms
by (intro contour_integrable_continuous_linepath continuous_intros)
   (auto simp add: closed_segment_def legacy_Complex_simps field_simps)

theorem perron_aux_1':
  fixes U :: real
  assumes hU: "0 < U" and Ha: "1 < a"
  shows "\<parallel>F a\<parallel> \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>) + a powr -U * T / (pi * U)"
proof -
  define f where "f \<equiv> \<lambda>s :: complex. a powr s / s"
  note assms' = cond assms this
  define P\<^sub>1 where "P\<^sub>1 \<equiv> linepath (Complex (-U) (-T)) (Complex b (-T))"
  define P\<^sub>2 where "P\<^sub>2 \<equiv> linepath (Complex b (-T)) (Complex b T)"
  define P\<^sub>3 where "P\<^sub>3 \<equiv> linepath (Complex b T) (Complex (-U) T)"
  define P\<^sub>4 where "P\<^sub>4 \<equiv> linepath (Complex (-U) T) (Complex (-U) (-T))"
  define P where "P \<equiv> P\<^sub>1 +++ P\<^sub>2 +++ P\<^sub>3 +++ P\<^sub>4"
  define I\<^sub>1 I\<^sub>2 I\<^sub>3 I\<^sub>4 where
    "I\<^sub>1 \<equiv> contour_integral P\<^sub>1 f" and "I\<^sub>2 \<equiv> contour_integral P\<^sub>2 f" and
    "I\<^sub>3 \<equiv> contour_integral P\<^sub>3 f" and "I\<^sub>4 \<equiv> contour_integral P\<^sub>4 f"
  define rpath where "rpath \<equiv> rectpath (Complex (-U) (-T)) (Complex b T)"
  note P_defs = P_def P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def
  note I_defs = I\<^sub>1_def I\<^sub>2_def I\<^sub>3_def I\<^sub>4_def
  have 1: "\<And>A B x. A \<subseteq> B \<Longrightarrow> x \<notin> A \<Longrightarrow> A \<subseteq> B - {x}" by auto
  have "path_image (rectpath (Complex (- U) (- T)) (Complex b T))
        \<subseteq> cbox (Complex (- U) (- T)) (Complex b T) - {0}"
    using assms'
    by (intro 1 path_image_rectpath_subset_cbox)
       (auto simp add: path_image_rectpath)
  moreover have "0 \<in> box (Complex (- U) (- T)) (Complex b T)"
    using assms' by (simp add: mem_box Basis_complex_def)
  ultimately have
    "((\<lambda>s. a powr s / (s - 0)) has_contour_integral
      2 * pi * \<i> * winding_number rpath 0 * a powr (0 :: complex)) rpath"
    "winding_number rpath 0 = 1"
    unfolding rpath_def
    by (intro Cauchy_integral_formula_convex_simple
              [where S = "cbox (Complex (-U) (-T)) (Complex b T)"])
       (auto intro!: assms' holomorphic_on_powr_right winding_number_rectpath
             simp add: mem_box Basis_complex_def)
  hence "(f has_contour_integral 2 * pi * \<i>) rpath" unfolding f_def using Ha by auto
  hence 2: "(f has_contour_integral 2 * pi * \<i>) P"
    unfolding rpath_def P_defs rectpath_def Let_def by simp
  hence "f contour_integrable_on P" by (intro has_contour_integral_integrable) (use 2 in auto)
  hence 3: "f contour_integrable_on P\<^sub>1" "f contour_integrable_on P\<^sub>2"
           "f contour_integrable_on P\<^sub>3" "f contour_integrable_on P\<^sub>4" unfolding P_defs by auto
  from 2 have "I\<^sub>1 + I\<^sub>2 + I\<^sub>3 + I\<^sub>4 = 2 * pi * \<i>" unfolding P_defs I_defs by (rule has_chain_integral_chain_integral4)
  hence "I\<^sub>2 - 2 * pi * \<i> = - (I\<^sub>1 + I\<^sub>3 + I\<^sub>4)" by (simp add: field_simps)
  hence "\<parallel>I\<^sub>2 - 2 * pi * \<i>\<parallel> = \<parallel>- (I\<^sub>1 + I\<^sub>3 + I\<^sub>4)\<parallel>" by auto
  also have "\<dots> = \<parallel>I\<^sub>1 + I\<^sub>3 + I\<^sub>4\<parallel>" by (rule norm_minus_cancel)
  also have "\<dots> \<le> \<parallel>I\<^sub>1 + I\<^sub>3\<parallel> + \<parallel>I\<^sub>4\<parallel>" by (rule norm_triangle_ineq)
  also have "\<dots> \<le> \<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>3\<parallel> + \<parallel>I\<^sub>4\<parallel>" using norm_triangle_ineq by auto
  finally have *: "\<parallel>I\<^sub>2 - 2 * pi * \<i>\<parallel> \<le> \<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>3\<parallel> + \<parallel>I\<^sub>4\<parallel>" .
  have I\<^sub>2_val: "\<parallel>I\<^sub>2 / (2 * pi * \<i>) - 1\<parallel> \<le> 1 / (2*pi) * (\<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>3\<parallel> + \<parallel>I\<^sub>4\<parallel>)"
  proof -
    have "I\<^sub>2 - 2 * pi * \<i> = (I\<^sub>2 / (2 * pi * \<i>) - 1) * (2 * pi * \<i>)" by (auto simp add: field_simps)
    hence "\<parallel>I\<^sub>2 - 2 * pi * \<i>\<parallel> = \<parallel>(I\<^sub>2 / (2 * pi * \<i>) - 1) * (2 * pi * \<i>)\<parallel>" by auto
    also have "\<dots> = \<parallel>I\<^sub>2 / (2 * pi * \<i>) - 1\<parallel> * (2*pi)" by (auto simp add: norm_mult)
    finally have "\<parallel>I\<^sub>2 / (2 * pi * \<i>) - 1\<parallel> = 1 / (2*pi) * \<parallel>I\<^sub>2 - 2 * pi * \<i>\<parallel>" by auto
    also have "\<dots> \<le> 1 / (2*pi) * (\<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>3\<parallel> + \<parallel>I\<^sub>4\<parallel>)"
      using * by (subst mult_le_cancel_left_pos) auto
    finally show ?thesis .
  qed
  define Q where "Q t \<equiv> linepath (Complex (-U) t) (Complex b t)" for t
  define g where "g t \<equiv> contour_integral (Q t) f" for t
  have Q_1: "(f has_contour_integral I\<^sub>1) (Q (-T))"
    using 3(1) unfolding P\<^sub>1_def I\<^sub>1_def Q_def
    by (rule has_contour_integral_integral)
  have Q_2: "(f has_contour_integral -I\<^sub>3) (Q T)"
    using 3(3) unfolding P\<^sub>3_def I\<^sub>3_def Q_def
    by (subst contour_integral_reversepath [symmetric],
        auto intro!: has_contour_integral_integral)
       (subst contour_integrable_reversepath_eq [symmetric], auto)
  have subst_I\<^sub>1_I\<^sub>3: "I\<^sub>1 = g (- T)" "I\<^sub>3 = - g T"
    using Q_1 Q_2 unfolding g_def by (auto simp add: contour_integral_unique)
  have g_bound: "\<parallel>g t\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
    when Ht: "\<bar>t\<bar> = T" for t
  proof -
    have "(f has_contour_integral g t) (Q t)" proof -
      consider "t = T" | "t = -T" using Ht by fastforce
      hence "f contour_integrable_on Q t" using Q_1 Q_2 by (metis has_contour_integral_integrable)
      thus ?thesis unfolding g_def by (rule has_contour_integral_integral)
    qed
    hence "((\<lambda>x. a powr (x + Im (Complex (-U) t) * \<i>) / (x + Im (Complex (-U) t) * \<i>)) has_integral (g t))
          {Re (Complex (-U) t) .. Re (Complex b t)}"
      unfolding Q_def f_def
      by (subst has_contour_integral_linepath_same_Im_iff [symmetric])
         (use hU Hb in auto)
    hence *: "((\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>)) has_integral g t) {-U..b}" by auto
    hence "\<parallel>g t\<parallel> = \<parallel>integral {-U..b} (\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>))\<parallel>" by (auto simp add: integral_unique)
    also have "\<dots> \<le> integral {-U..b} (\<lambda>x. a powr x / T)"
    proof (rule integral_norm_bound_integral)
      show "(\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>)) integrable_on {-U..b}" using * by auto
      have "(\<lambda>x. a powr x / (of_real T)) integrable_on {-U..b}"
        by (intro iffD2 [OF integrable_on_cdivide_iff] powr_integrable) (use hU Ha Hb hT' in auto)
      thus "(\<lambda>x. a powr x / T) integrable_on {-U..b}" by auto
    next
      fix x assume "x \<in> {-U..b}"
      have "\<parallel>a powr (x + t * \<i>)\<parallel> = Re a powr Re (x + t * \<i>)" by (rule norm_powr_real_powr) (use Ha in auto)
      also have "\<dots> = a powr x" by auto
      finally have *: "\<parallel>a powr (x + t * \<i>)\<parallel> = a powr x" .
      have "T = \<bar>Im (x + t * \<i>)\<bar>" using Ht by auto
      also have "\<dots> \<le> \<parallel>x + t * \<i>\<parallel>" by (rule abs_Im_le_cmod)
      finally have "T \<le> \<parallel>x + t * \<i>\<parallel>" .
      with * show "\<parallel>a powr (x + t * \<i>) / (x + t * \<i>)\<parallel> \<le> a powr x / T"
        by (subst norm_divide) (rule frac_le, use assms' in auto)
    qed
    also have "\<dots> = integral {-U..b} (\<lambda>x. a powr x) / T" by auto
    also have "\<dots> \<le> a powr b / (T * \<bar>ln a\<bar>)"
    proof -
      have "integral {-U..b} (\<lambda>x. a powr x) \<le> a powr b / \<bar>ln a\<bar>"
        by (rule powr_integral_bound_gt_1) (use hU Ha Hb in auto)
      thus ?thesis using hT' by (auto simp add: field_simps)
    qed
    finally show ?thesis .
  qed
  have "\<parallel>I\<^sub>4\<parallel> \<le> a powr -U / U * \<parallel>Complex (- U) (- T) - Complex (- U) T\<parallel>"
  proof -
    have "f contour_integrable_on P\<^sub>4" by (rule 3)
    moreover have "0 \<le> a powr - U / U" using hU by auto
    moreover have "\<parallel>f z\<parallel> \<le> a powr - U / U"
      when *: "z \<in> closed_segment (Complex (- U) T) (Complex (- U) (- T))" for z
    proof -
      from * have Re_z: "Re z = - U"
        unfolding closed_segment_def
        by (auto simp add: legacy_Complex_simps field_simps)
      hence "U = \<bar>Re z\<bar>" using hU by auto
      also have "\<dots> \<le> \<parallel>z\<parallel>" by (rule abs_Re_le_cmod)
      finally have zmod: "U \<le> \<parallel>z\<parallel>" .
      have "\<parallel>f z\<parallel> = \<parallel>a powr z\<parallel> / \<parallel>z\<parallel>" unfolding f_def by (rule norm_divide)
      also have "\<dots> \<le> a powr - U / U"
        by (subst norm_powr_real_powr, use Ha in auto)
           (rule frac_le, use hU Re_z zmod in auto)
      finally show ?thesis .
    qed
    ultimately show ?thesis unfolding I\<^sub>4_def P\<^sub>4_def by (rule contour_integral_bound_linepath)
  qed
  also have "\<dots> = a powr -U / U * (2 * T)"
  proof -
    have "sqrt ((2 * T)\<^sup>2) = \<bar>2 * T\<bar>" by (rule real_sqrt_abs)
    thus ?thesis using hT' by (auto simp add: field_simps legacy_Complex_simps)
  qed
  finally have I\<^sub>4_bound: "\<parallel>I\<^sub>4\<parallel> \<le> a powr -U / U * (2 * T)" .
  have "\<parallel>I\<^sub>2 / (2 * pi * \<i>) - 1\<parallel> \<le> 1 / (2*pi) * (\<parallel>g (- T)\<parallel> + \<parallel>- g T\<parallel> + \<parallel>I\<^sub>4\<parallel>)"
    using I\<^sub>2_val subst_I\<^sub>1_I\<^sub>3 by auto
  also have "\<dots> \<le> 1 / (2*pi) * (2 * a powr b / (T * \<bar>ln a\<bar>) + a powr -U / U * (2*T))"
  proof -
    have "\<parallel>g T\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
         "\<parallel>g (- T)\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
      using hT' by (auto intro: g_bound)
    hence "\<parallel>g (- T)\<parallel> + \<parallel>- g T\<parallel> + \<parallel>I\<^sub>4\<parallel> \<le> 2 * a powr b / (T * \<bar>ln a\<bar>) + a powr -U / U * (2*T)"
      using I\<^sub>4_bound by auto
    thus ?thesis by (auto simp add: field_simps)
  qed
  also have "\<dots> = 1 / pi * a powr b / (T * \<bar>ln a\<bar>) + a powr -U * T / (pi * U)"
    using hT' by (auto simp add: field_simps)
  finally show ?thesis
    using Ha unfolding I\<^sub>2_def P\<^sub>2_def f_def F_def path_def by auto
qed

theorem perron_aux_1:
  assumes Ha: "1 < a"
  shows "\<parallel>F a\<parallel> \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>)" (is "_ \<le> ?x")
proof -
  let ?y = "\<lambda>U :: real. a powr -U * T / (pi * U)"
  have "((\<lambda>U :: real. ?x) \<longlongrightarrow> ?x) at_top" by auto
  moreover have "((\<lambda>U. ?y U) \<longlongrightarrow> 0) at_top" using Ha by real_asymp
  ultimately have "((\<lambda>U. ?x + ?y U) \<longlongrightarrow> ?x + 0) at_top" by (rule tendsto_add)
  hence "((\<lambda>U. ?x + ?y U) \<longlongrightarrow> ?x) at_top" by auto
  moreover have "\<parallel>F a\<parallel> \<le> ?x + ?y U" when hU: "0 < U" for U
    by (subst perron_aux_1' [OF hU Ha], standard)
  hence "\<forall>\<^sub>F U in at_top. \<parallel>F a\<parallel> \<le> ?x + ?y U"
    by (rule eventually_at_top_linorderI')
  ultimately show ?thesis
    by (intro tendsto_lowerbound) auto
qed

theorem perron_aux_2':
  fixes U :: real
  assumes hU: "0 < U" "b < U" and Ha: "0 < a \<and> a < 1"
  shows "\<parallel>F a\<parallel> \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>) + a powr U * T / (pi * U)"
proof -
  define f where "f \<equiv> \<lambda>s :: complex. a powr s / s"
  note assms' = cond assms hU
  define P\<^sub>1 where "P\<^sub>1 \<equiv> linepath (Complex b (-T)) (Complex U (-T))"
  define P\<^sub>2 where "P\<^sub>2 \<equiv> linepath (Complex U (-T)) (Complex U T)"
  define P\<^sub>3 where "P\<^sub>3 \<equiv> linepath (Complex U T) (Complex b T)"
  define P\<^sub>4 where "P\<^sub>4 \<equiv> linepath (Complex b T) (Complex b (-T))"
  define P where "P \<equiv> P\<^sub>1 +++ P\<^sub>2 +++ P\<^sub>3 +++ P\<^sub>4"
  define I\<^sub>1 I\<^sub>2 I\<^sub>3 I\<^sub>4 where
    "I\<^sub>1 \<equiv> contour_integral P\<^sub>1 f" and "I\<^sub>2 \<equiv> contour_integral P\<^sub>2 f" and
    "I\<^sub>3 \<equiv> contour_integral P\<^sub>3 f" and "I\<^sub>4 \<equiv> contour_integral P\<^sub>4 f"
  define rpath where "rpath \<equiv> rectpath (Complex b (- T)) (Complex U T)"
  note P_defs = P_def P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def
  note I_defs = I\<^sub>1_def I\<^sub>2_def I\<^sub>3_def I\<^sub>4_def
  have "path_image (rectpath (Complex b (- T)) (Complex U T)) \<subseteq> cbox (Complex b (- T)) (Complex U T)"
    by (intro path_image_rectpath_subset_cbox) (use assms' in auto)
  moreover have "0 \<notin> cbox (Complex b (- T)) (Complex U T)"
    using Hb unfolding cbox_def by (auto simp add: Basis_complex_def)
  ultimately have "((\<lambda>s. a powr s / (s - 0)) has_contour_integral 0) rpath"
    unfolding rpath_def
    by (intro Cauchy_theorem_convex_simple
              [where S = "cbox (Complex b (- T)) (Complex U T)"])
       (auto intro!: holomorphic_on_powr_right holomorphic_on_divide)
  hence "(f has_contour_integral 0) rpath" unfolding f_def using Ha by auto
  hence 1: "(f has_contour_integral 0) P" unfolding rpath_def P_defs rectpath_def Let_def by simp
  hence "f contour_integrable_on P" by (intro has_contour_integral_integrable) (use 1 in auto)
  hence 2: "f contour_integrable_on P\<^sub>1" "f contour_integrable_on P\<^sub>2"
           "f contour_integrable_on P\<^sub>3" "f contour_integrable_on P\<^sub>4" unfolding P_defs by auto
  from 1 have "I\<^sub>1 + I\<^sub>2 + I\<^sub>3 + I\<^sub>4 = 0" unfolding P_defs I_defs by (rule has_chain_integral_chain_integral4)
  hence "I\<^sub>4 = - (I\<^sub>1 + I\<^sub>2 + I\<^sub>3)" by (metis neg_eq_iff_add_eq_0)
  hence "\<parallel>I\<^sub>4\<parallel> = \<parallel>- (I\<^sub>1 + I\<^sub>2 + I\<^sub>3)\<parallel>" by auto
  also have "\<dots> = \<parallel>I\<^sub>1 + I\<^sub>2 + I\<^sub>3\<parallel>" by (rule norm_minus_cancel)
  also have "\<dots> \<le> \<parallel>I\<^sub>1 + I\<^sub>2\<parallel> + \<parallel>I\<^sub>3\<parallel>" by (rule norm_triangle_ineq)
  also have "\<dots> \<le> \<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>2\<parallel> + \<parallel>I\<^sub>3\<parallel>" using norm_triangle_ineq by auto
  finally have "\<parallel>I\<^sub>4\<parallel> \<le> \<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>2\<parallel> + \<parallel>I\<^sub>3\<parallel>" .
  hence I\<^sub>4_val: "\<parallel>I\<^sub>4 / (2 * pi * \<i>)\<parallel> \<le> 1 / (2*pi) * (\<parallel>I\<^sub>1\<parallel> + \<parallel>I\<^sub>2\<parallel> + \<parallel>I\<^sub>3\<parallel>)"
    by (auto simp add: norm_divide norm_mult field_simps)
  define Q where "Q t \<equiv> linepath (Complex b t) (Complex U t)" for t
  define g where "g t \<equiv> contour_integral (Q t) f" for t
  have Q_1: "(f has_contour_integral I\<^sub>1) (Q (-T))"
    using 2(1) unfolding P\<^sub>1_def I\<^sub>1_def Q_def
    by (rule has_contour_integral_integral)
  have Q_2: "(f has_contour_integral -I\<^sub>3) (Q T)"
    using 2(3) unfolding P\<^sub>3_def I\<^sub>3_def Q_def
    by (subst contour_integral_reversepath [symmetric],
        auto intro!: has_contour_integral_integral)
       (subst contour_integrable_reversepath_eq [symmetric], auto)
  have subst_I\<^sub>1_I\<^sub>3: "I\<^sub>1 = g (- T)" "I\<^sub>3 = - g T"
    using Q_1 Q_2 unfolding g_def by (auto simp add: contour_integral_unique)
  have g_bound: "\<parallel>g t\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
    when Ht: "\<bar>t\<bar> = T" for t
  proof -
    have "(f has_contour_integral g t) (Q t)" proof -
      consider "t = T" | "t = -T" using Ht by fastforce
      hence "f contour_integrable_on Q t" using Q_1 Q_2 by (metis has_contour_integral_integrable)
      thus ?thesis unfolding g_def by (rule has_contour_integral_integral)
    qed
    hence "((\<lambda>x. a powr (x + Im (Complex b t) * \<i>) / (x + Im (Complex b t) * \<i>)) has_integral (g t))
          {Re (Complex b t) .. Re (Complex U t)}"
      unfolding Q_def f_def
      by (subst has_contour_integral_linepath_same_Im_iff [symmetric])
         (use assms' in auto)
    hence *: "((\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>)) has_integral g t) {b..U}" by auto
    hence "\<parallel>g t\<parallel> = \<parallel>integral {b..U} (\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>))\<parallel>" by (auto simp add: integral_unique)
    also have "\<dots> \<le> integral {b..U} (\<lambda>x. a powr x / T)"
    proof (rule integral_norm_bound_integral)
      show "(\<lambda>x. a powr (x + t * \<i>) / (x + t * \<i>)) integrable_on {b..U}" using * by auto
      have "(\<lambda>x. a powr x / (of_real T)) integrable_on {b..U}"
        by (intro iffD2 [OF integrable_on_cdivide_iff] powr_integrable) (use assms' in auto)
      thus "(\<lambda>x. a powr x / T) integrable_on {b..U}" by auto
    next
      fix x assume "x \<in> {b..U}"
      have "\<parallel>a powr (x + t * \<i>)\<parallel> = Re a powr Re (x + t * \<i>)" by (rule norm_powr_real_powr) (use Ha in auto)
      also have "\<dots> = a powr x" by auto
      finally have 1: "\<parallel>a powr (x + t * \<i>)\<parallel> = a powr x" .
      have "T = \<bar>Im (x + t * \<i>)\<bar>" using Ht by auto
      also have "\<dots> \<le> \<parallel>x + t * \<i>\<parallel>" by (rule abs_Im_le_cmod)
      finally have 2: "T \<le> \<parallel>x + t * \<i>\<parallel>" .
      from 1 2 show "\<parallel>a powr (x + t * \<i>) / (x + t * \<i>)\<parallel> \<le> a powr x / T"
        by (subst norm_divide) (rule frac_le, use hT' in auto)
    qed
    also have "\<dots> = integral {b..U} (\<lambda>x. a powr x) / T" by auto
    also have "\<dots> \<le> a powr b / (T * \<bar>ln a\<bar>)"
    proof -
      have "integral {b..U} (\<lambda>x. a powr x) \<le> a powr b / \<bar>ln a\<bar>"
        by (rule powr_integral_bound_lt_1) (use assms' in auto)
      thus ?thesis using hT' by (auto simp add: field_simps)
    qed
    finally show ?thesis .
  qed
  have "\<parallel>I\<^sub>2\<parallel> \<le> a powr U / U * \<parallel>Complex U T - Complex U (- T)\<parallel>"
  proof -
    have "f contour_integrable_on P\<^sub>2" by (rule 2)
    moreover have "0 \<le> a powr U / U" using hU by auto
    moreover have "\<parallel>f z\<parallel> \<le> a powr U / U"
      when *: "z \<in> closed_segment (Complex U (- T)) (Complex U T)" for z
    proof -
      from * have Re_z: "Re z = U"
        unfolding closed_segment_def
        by (auto simp add: legacy_Complex_simps field_simps)
      hence "U = \<bar>Re z\<bar>" using hU by auto
      also have "\<dots> \<le> \<parallel>z\<parallel>" by (rule abs_Re_le_cmod)
      finally have zmod: "U \<le> \<parallel>z\<parallel>" .
      have "\<parallel>f z\<parallel> = \<parallel>a powr z\<parallel> / \<parallel>z\<parallel>" unfolding f_def by (rule norm_divide)
      also have "\<dots> \<le> a powr U / U"
        by (subst norm_powr_real_powr, use Ha in auto)
           (rule frac_le, use hU Re_z zmod in auto)
      finally show ?thesis .
    qed
    ultimately show ?thesis unfolding I\<^sub>2_def P\<^sub>2_def by (rule contour_integral_bound_linepath)
  qed
  also have "\<dots> \<le> a powr U / U * (2 * T)"
  proof -
    have "sqrt ((2 * T)\<^sup>2) = \<bar>2 * T\<bar>" by (rule real_sqrt_abs)
    thus ?thesis using hT' by (simp add: field_simps legacy_Complex_simps)
  qed
  finally have I\<^sub>2_bound: "\<parallel>I\<^sub>2\<parallel> \<le> a powr U / U * (2 * T)" .
  have "\<parallel>I\<^sub>4 / (2 * pi * \<i>)\<parallel> \<le> 1 / (2*pi) * (\<parallel>g (- T)\<parallel> + \<parallel>I\<^sub>2\<parallel> + \<parallel>- g T\<parallel>)"
    using I\<^sub>4_val subst_I\<^sub>1_I\<^sub>3 by auto
  also have "\<dots> \<le> 1 / (2*pi) * (2 * a powr b / (T * \<bar>ln a\<bar>) + a powr U / U * (2*T))"
  proof -
    have "\<parallel>g T\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
         "\<parallel>g (- T)\<parallel> \<le> a powr b / (T * \<bar>ln a\<bar>)"
      using hT' by (auto intro: g_bound)
    hence "\<parallel>g (- T)\<parallel> + \<parallel>- g T\<parallel> + \<parallel>I\<^sub>2\<parallel> \<le> 2 * a powr b / (T * \<bar>ln a\<bar>) + a powr U / U * (2*T)"
      using I\<^sub>2_bound by auto
    thus ?thesis by (auto simp add: field_simps)
  qed
  also have "\<dots> = 1 / pi * a powr b / (T * \<bar>ln a\<bar>) + a powr U * T / (pi * U)"
    using hT' by (auto simp add: field_simps)
  finally have "\<parallel>1 / (2 * pi * \<i>) * contour_integral (reversepath P\<^sub>4) f\<parallel>
    \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>) + a powr U * T / (pi * U)"
    unfolding I\<^sub>4_def P\<^sub>4_def by (subst contour_integral_reversepath) auto
  thus ?thesis using Ha unfolding I\<^sub>4_def P\<^sub>4_def f_def F_def path_def by auto
qed

theorem perron_aux_2:
  assumes Ha: "0 < a \<and> a < 1"
  shows "\<parallel>F a\<parallel> \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>)" (is "_ \<le> ?x")
proof -
  let ?y = "\<lambda>U :: real. a powr U * T / (pi * U)"
  have "((\<lambda>U :: real. ?x) \<longlongrightarrow> ?x) at_top" by auto
  moreover have "((\<lambda>U. ?y U) \<longlongrightarrow> 0) at_top" using Ha by real_asymp
  ultimately have "((\<lambda>U. ?x + ?y U) \<longlongrightarrow> ?x + 0) at_top" by (rule tendsto_add)
  hence "((\<lambda>U. ?x + ?y U) \<longlongrightarrow> ?x) at_top" by auto
  moreover have "\<parallel>F a\<parallel> \<le> ?x + ?y U" when hU: "0 < U" "b < U" for U
    by (subst perron_aux_2' [OF hU Ha], standard)
  hence "\<forall>\<^sub>F U in at_top. \<parallel>F a\<parallel> \<le> ?x + ?y U"
    by (rule eventually_at_top_linorderI') (use Hb in auto)
  ultimately show ?thesis
    by (intro tendsto_lowerbound) auto
qed

theorem perron_aux_3:
  assumes Ha: "0 < a"
  shows "\<parallel>1 / (2 * pi * \<i>) * contour_integral path (\<lambda>s. a powr s / s)\<parallel> \<le> a powr b * ln (1 + T / b)"
proof -
  have "\<parallel>1 / (2 * pi * \<i>) * contour_integral (linepath (Complex b (-T)) (Complex b T)) (\<lambda>s. 1 * a powr s / s)\<parallel>
       \<le> 1 * a powr b * ln (1 + T / b)"
    by (rule perron_aux_3') (auto intro: Ha cond perron_integrable)
  thus ?thesis unfolding path_def by auto
qed

theorem perron_aux':
  assumes Ha: "0 < a"
  shows "\<parallel>F a\<parallel> \<le> a powr b * r a"
proof -
  note assms' = assms cond
  define P where "P \<equiv> 1 / (2 * pi * \<i>) * contour_integral path (\<lambda>s. a powr s / s)"
  have lm_1: "1 + ln (1 + T / b) \<le> 2 + ln (T / b)"
  proof -
    have "1 \<le> T / b" using hT Hb by auto
    hence "1 + T / b \<le> 2 * (T / b)" by auto
    hence "ln (1 + T / b) \<le> ln 2 + ln (T / b)" by (subst ln_mult [symmetric]) auto
    thus ?thesis using ln_2_less_1 by auto
  qed
  have *: "\<parallel>F a\<parallel> \<le> a powr b * (2 + ln (T / b))"
  proof (cases "1 \<le> a")
    assume Ha': "1 \<le> a"
    have "\<parallel>P - 1\<parallel> \<le> \<parallel>P\<parallel> + 1" by (simp add: norm_triangle_le_diff)
    also have "\<dots> \<le> a powr b * ln (1 + T / b) + 1"
    proof -
      have "\<parallel>P\<parallel> \<le> a powr b * ln (1 + T / b)"
        unfolding P_def by (intro perron_aux_3 assms')
      thus ?thesis by auto
    qed
    also have "\<dots> \<le> a powr b * (2 + ln (T / b))"
    proof -
      have "1 = a powr 0" using Ha' by auto
      also have "a powr 0 \<le> a powr b" using Ha' Hb by (intro powr_mono) auto
      finally have "a powr b * ln (1 + T / b) + 1 \<le> a powr b * (1 + ln (1 + T / b))"
        by (auto simp add: algebra_simps)
      also have "\<dots> \<le> a powr b * (2 + ln (T / b))" using Ha' lm_1 by auto
      finally show ?thesis .
    qed
    finally show ?thesis using Ha' unfolding F_def P_def by auto
  next
    assume Ha': "\<not> 1 \<le> a"
    hence "\<parallel>P\<parallel> \<le> a powr b * ln (1 + T / b)"
      unfolding P_def by (intro perron_aux_3 assms')
    also have "\<dots> \<le> a powr b * (2 + ln (T / b))"
      by (rule mult_left_mono) (use lm_1 in auto)
    finally show ?thesis using Ha' unfolding F_def P_def by auto
  qed
  consider "0 < a \<and> a \<noteq> 1" | "a = 1" using Ha by linarith
  thus ?thesis proof cases
    define c where "c = 1 / 2 * a powr b / (T * \<bar>ln a\<bar>)"
    assume Ha': "0 < a \<and> a \<noteq> 1"
    hence "(0 < a \<and> a < 1) \<or> a > 1" by auto
    hence "\<parallel>F a\<parallel> \<le> 1 / pi * a powr b / (T * \<bar>ln a\<bar>)"
      using perron_aux_1 perron_aux_2 by auto
    also have "\<dots> \<le> c" unfolding c_def
      using Ha' hT' pi_gt3 by (auto simp add: field_simps)
    finally have "\<parallel>F a\<parallel> \<le> c" .
    hence "\<parallel>F a\<parallel> \<le> min c (a powr b * (2 + ln (T / b)))" using * by auto
    also have "\<dots> = a powr b * r a"
      unfolding r_def c_def using Ha' by auto (subst min_mult_distrib_left, auto)
    finally show ?thesis using Ha' unfolding P_def by auto
  next
    assume Ha': "a = 1"
    with * show ?thesis unfolding r_def by auto
  qed
qed

lemma r_bound:
  assumes Hn: "1 \<le> n"
  shows "r (x / n) \<le> H / T + (if n \<in> region then 2 + ln (T / b) else 0)"
proof (cases "n \<in> region")
  assume *: "n \<notin> region"
  then consider "n < x - x / H" | "x + x / H < n" unfolding region_def by auto
  hence "1 / \<bar>ln (x / n)\<bar> \<le> 2 * H"
  proof cases
    have hH': "1 / (1 - 1 / H) > 1" using hH by auto
    case 1 hence "x / n > x / (x - x / H)"
      using Hx hH Hn by (intro divide_strict_left_mono) auto
    also have "x / (x - x / H) = 1 / (1 - 1 / H)"
      using Hx hH by (auto simp add: field_simps)
    finally have xn: "x / n > 1 / (1 - 1 / H)" .
    moreover have xn': "x / n > 1" using xn hH' by linarith
    ultimately have "\<bar>ln (x / n)\<bar> > ln (1 / (1 - 1 / H))"
      using hH Hx Hn by auto
    hence "1 / \<bar>ln (x / n)\<bar> < 1 / ln (1 / (1 - 1 / H))"
      using xn' hH' by (intro divide_strict_left_mono mult_pos_pos ln_gt_zero) auto
    also have "\<dots> \<le> H" proof -
      have "ln (1 - 1 / H) \<le> - (1 / H)"
        using hH by (intro ln_one_minus_pos_upper_bound) auto
      hence "-1 / ln (1 - 1 / H) \<le> -1 / (- (1 / H))"
        using hH by (intro divide_left_mono_neg) (auto intro: divide_neg_pos)
      also have "... = H" by auto
      finally show ?thesis
        by (subst (2) inverse_eq_divide [symmetric])
           (subst ln_inverse, use hH in auto)
    qed
    finally show ?thesis using hH by auto
  next
    case 2 hence "x / n < x / (x + x / H)"
      using Hx hH Hn by (auto intro!: divide_strict_left_mono mult_pos_pos add_pos_pos)
    also have "\<dots> = 1 / (1 + 1 / H)"
    proof -
      have "0 < x + x * H" using Hx hH by (auto intro: add_pos_pos)
      thus ?thesis using Hx hH by (auto simp add: field_simps)
    qed
    finally have xn: "x / n < 1 / (1 + 1 / H)" .
    also have hH': "\<dots> < 1" using hH by (auto simp add: field_simps)
    finally have xn': "0 < x / n \<and> x / n < 1" using Hx Hn by auto
    have "1 / \<bar>ln (x / n)\<bar> = -1 / ln (x / n)"
      using xn' by (auto simp add: field_simps)
    also have "\<dots> \<le> 2 * H" proof -
      have "ln (x / n) < ln (1 / (1 + 1 / H))"
        using xn xn' by (subst ln_less_cancel_iff) (blast, linarith)
      also have "\<dots> = - ln (1 + 1 / H)"
        by (subst (1) inverse_eq_divide [symmetric])
           (subst ln_inverse, intro add_pos_pos, use hH in auto)
      also have "\<dots> \<le> - 1 / (2 * H)"
      proof -
        have "1 / H - (1 / H)\<^sup>2 \<le> ln (1 + 1 / H)"
          by (rule ln_one_plus_pos_lower_bound) (use hH in auto)
        hence "- ln (1 + 1 / H) \<le> - 1 / H + (1 / H)\<^sup>2" by auto
        also have "\<dots> \<le> - 1 / (2 * H)"
          using hH unfolding power2_eq_square by (auto simp add: field_simps)
        finally show ?thesis .
      qed
      finally have "-1 / ln (x / n) \<le> -1 / (-1 / (2 * H))"
        by (intro divide_left_mono_neg) (insert xn' hH, auto simp add: field_simps)
      thus ?thesis by auto
    qed
    finally show ?thesis .
  qed
  hence "(1 / \<bar>ln (x / n)\<bar>) / (2 * T) \<le> (2 * H) / (2 * T)"
    using hT' by (intro divide_right_mono) auto
  hence "1 / (2 * T * \<bar>ln (x / n)\<bar>) \<le> H / T"
    by (simp add: field_simps)
  moreover have "x / n \<noteq> 1" using * hH unfolding region_def by auto
  ultimately show ?thesis unfolding r_def using * by auto
next
  assume *: "n \<in> region"
  moreover have "2 + ln (T / b) \<le> H / T + (2 + ln (T / b))"
    using hH hT' by auto
  ultimately show ?thesis unfolding r_def by auto
qed

theorem perron_aux:
  assumes Hn: "0 < n"
  shows "\<parallel>F' n\<parallel> \<le> 1 / n nat_powr b * (x powr b * H / T)
    + (if n \<in> region then 3 * (2 + ln (T / b)) else 0)" (is "?P \<le> ?Q")
proof -
  have "\<parallel>F (x / n)\<parallel> \<le> (x / n) powr b * r (x / n)"
    by (rule perron_aux') (use Hx Hn in auto)
  also have "\<dots> \<le> (x / n) powr b * (H / T + (if n \<in> region then 2 + ln (T / b) else 0))"
    by (intro mult_left_mono r_bound) (use Hn in auto)
  also have "\<dots> \<le> ?Q"
  proof -
    have *: "(x / n) powr b * (H / T) = 1 / n nat_powr b * (x powr b * H / T)"
      using Hx Hn by (subst powr_divide) (auto simp add: field_simps)
    moreover have "(x / n) powr b * (H / T + (2 + ln (T / b)))
      \<le> 1 / n nat_powr b * (x powr b * H / T) + 3 * (2 + ln (T / b))"
      when Hn': "n \<in> region"
    proof -
      have "(x / n) powr b \<le> 3"
      proof -
        have "x - x / H \<le> n" using Hn' unfolding region_def by auto
        moreover have "x / H < x / 1" using hH Hx by (intro divide_strict_left_mono) auto
        ultimately have "x / n \<le> x / (x - x / H)"
          using Hx hH Hn by (intro divide_left_mono mult_pos_pos) auto
        also have "\<dots> = 1 + 1 / (H - 1)"
          using Hx hH by (auto simp add: field_simps)
        finally have "(x / n) powr b \<le> (1 + 1 / (H - 1)) powr b"
          using Hx Hn Hb by (intro powr_mono2) auto
        also have "\<dots> \<le> exp (b / (H - 1))"
        proof -
          have "ln (1 + 1 / (H - 1)) \<le> 1 / (H - 1)"
            using hH by (intro ln_add_one_self_le_self) auto
          hence "b * ln (1 + 1 / (H - 1)) \<le> b * (1 / (H - 1))"
            using Hb by (intro mult_left_mono) auto
          thus ?thesis unfolding powr_def by auto
        qed
        also have "\<dots> \<le> exp 1" using Hb hH' by auto
        also have "\<dots> \<le> 3" by (rule exp_le)
        finally show ?thesis .
      qed
      moreover have "0 \<le> ln (T / b)" using hT Hb by (auto intro!: ln_ge_zero)
      ultimately show ?thesis using hT
        by (subst ring_distribs, subst *, subst add_le_cancel_left)
           (intro mult_right_mono, auto intro!: add_nonneg_nonneg)
    qed
    ultimately show ?thesis by auto
  qed
  finally show ?thesis unfolding F'_def .
qed

definition a where "a n \<equiv> fds_nth f n"

theorem finite_region: "finite region"
  unfolding region_def by (subst nat_le_real_iff) auto

theorem zero_notin_region: "0 \<notin> region"
  unfolding region_def using hH Hx by (auto simp add: field_simps)

theorem perron_bound:
  "\<parallel>\<Sum>`n \<ge> 1. a n * F' n\<parallel> \<le> x powr b * H * B / T
    + 3 * (2 + ln (T / b)) * (\<Sum>n\<in>region. \<parallel>a n\<parallel>)"
proof -
  define M where "M \<equiv> 3 * (2 + ln (T / b))"
  have sum_1: "(\<lambda>n. \<parallel>a n / n nat_powr (b :: complex)\<parallel>) subsummable {1..}"
    unfolding a_def
    by (fold nat_power_complex_def)
       (intro fds_abs_subsummable fds_abs_converges, auto, rule Hb')
  hence sum_2: "(\<lambda>n. \<parallel>a n\<parallel> * 1 / n nat_powr b) subsummable {1..}"
  proof -
    have "\<parallel>a n / n nat_powr (b :: complex)\<parallel> = \<parallel>a n\<parallel> * 1 / n nat_powr b" for n
      by (auto simp add: norm_divide field_simps norm_nat_power)
    thus ?thesis using sum_1 by auto
  qed
  hence sum_3: "(\<lambda>n. \<parallel>a n\<parallel> * 1 / n nat_powr b * (x powr b * H / T)) subsummable {1..}"
    by (rule subsummable_mult2)
  moreover have sum_4: "(\<lambda>n. if n \<in> region then M * \<parallel>a n\<parallel> else 0) subsummable {1..}"
    by (intro has_subsum_summable, rule has_subsum_If_finite)
       (insert finite_region, auto)
  moreover have "\<parallel>a n * F' n\<parallel>
    \<le> \<parallel>a n\<parallel> * 1 / n nat_powr b * (x powr b * H / T)
    + (if n \<in> region then M * \<parallel>a n\<parallel> else 0)" (is "?x' \<le> ?x")
    when "n \<in> {1..}" for n
  proof -
    have "\<parallel>a n * F' n\<parallel> \<le> \<parallel>a n\<parallel> *
      (1 / n nat_powr b * (x powr b * H / T) + (if n \<in> region then M else 0))"
      unfolding M_def
      by (subst norm_mult)
         (intro mult_left_mono perron_aux, use that in auto)
    also have "\<dots> = ?x" by (simp add: field_simps)
    finally show ?thesis .
  qed
  ultimately have "\<parallel>\<Sum>`n \<ge> 1. a n * F' n\<parallel>
    \<le> (\<Sum>`n \<ge> 1. \<parallel>a n\<parallel> * 1 / n nat_powr b * (x powr b * H / T)
    + (if n \<in> region then M * \<parallel>a n\<parallel> else 0))"
    by (intro subsum_norm_bound subsummable_add)
  also have "\<dots> \<le> x powr b * H * B / T + M * (\<Sum>n\<in>region. \<parallel>a n\<parallel>)"
  proof -
    have "(\<Sum>`n \<ge> 1. (if n \<in> region then M * \<parallel>a n\<parallel> else 0))
        = (\<Sum>n \<in> region \<inter> {1..}. M * \<parallel>a n\<parallel>)"
      by (intro subsumI [symmetric] has_subsum_If_finite_set finite_region)
    also have "\<dots> = M * (\<Sum>n\<in>region. \<parallel>a n\<parallel>)"
    proof -
      have "region \<inter> {1..} = region"
        using zero_notin_region zero_less_iff_neq_zero by (auto intro: Suc_leI)
      thus ?thesis by (subst sum_distrib_left) (use zero_notin_region in auto)
    qed
    also have
      "(\<Sum>`n \<ge> 1. \<parallel>a n\<parallel> * 1 / n nat_powr b * (x powr b * H / T))
      \<le> x powr b * H * B / T"
      by (subst subsum_mult2, rule sum_2, insert hB hH hT', fold a_def)
         (auto simp add: field_simps, subst (1) mult.commute, auto intro: mult_right_mono)
    ultimately show ?thesis
      by (subst subsum_add [symmetric]) ((rule sum_3 sum_4)+, auto)
  qed
  finally show ?thesis unfolding M_def .
qed

lemma path_image_conv:
  assumes "s \<in> img_path"
  shows "conv_abscissa f < s \<bullet> 1"
proof -
  from assms have "Re s = b"
    unfolding img_path_def path_def
    by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)
  thus ?thesis using Hb' conv_le_abs_conv_abscissa [of f] by auto
qed

lemma converge_on_path:
  assumes "s \<in> img_path"
  shows "fds_converges f s"
  by (intro fds_converges path_image_conv assms)

lemma summable_on_path:
  assumes "s \<in> img_path"
  shows "(\<lambda>n. a n / n nat_powr s) subsummable {1..}"
  unfolding a_def by (intro eval_fds_complex_subsum(2) converge_on_path assms)

lemma zero_notin_path:
  shows "0 \<notin> closed_segment (Complex b (- T)) (Complex b T)"
  using Hb unfolding img_path_def path_def
  by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)

theorem perron:
  "(\<lambda>s. eval_fds f s * x powr s / s) contour_integrable_on path"
  "\<parallel>sum_upto a x - 1 / (2 * pi * \<i>) * contour_integral path (\<lambda>s. eval_fds f s * x powr s / s)\<parallel>
    \<le> x powr b * H * B / T + 3 * (2 + ln (T / b)) * (\<Sum>n\<in>region. \<parallel>a n\<parallel>)"
proof (goal_cases)
  define g where "g s \<equiv> eval_fds f s * x powr s / s" for s :: complex
  define h where "h s n \<equiv> a n / n nat_powr s * (x powr s / s)" for s :: complex and n :: nat
  define G where "G n \<equiv> contour_integral path (\<lambda>s. (x / n) powr s / s)" for n :: nat
  define H where "H n \<equiv> 1 / (2 * pi * \<i>) * G n" for n :: nat
  have h_integrable: "(\<lambda>s. h s n) contour_integrable_on path" when "0 < n" for n
    using Hb Hx unfolding path_def h_def
    by (intro contour_integrable_continuous_linepath continuous_intros)
       (use that zero_notin_path in auto)
  have "contour_integral path g = contour_integral path (\<lambda>s. \<Sum>`n \<ge> 1. h s n)"
  proof (rule contour_integral_eq, fold img_path_def)
    fix s assume *: "s \<in> img_path"
    hence "g s = (\<Sum>`n \<ge> 1. a n / n nat_powr s) * (x powr s / s)"
      unfolding g_def a_def
      by (subst eval_fds_complex_subsum) (auto intro!: converge_on_path)
    also have "\<dots> = (\<Sum>`n \<ge> 1. a n / n nat_powr s * (x powr s / s))"
      by (intro subsum_mult2 [symmetric] summable) (intro summable_on_path *)
    finally show "g s = (\<Sum>`n \<ge> 1. h s n)" unfolding h_def .
  qed
  also have
    sum_1: "(\<lambda>n. contour_integral path (\<lambda>s. h s n)) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. contour_integral path (\<lambda>s. h s n))"
  proof (goal_cases)
    have "((\<lambda>N. contour_integral path (\<lambda>s. sum (h s) {1..N}))
      \<longlongrightarrow> contour_integral path (\<lambda>s. subsum (h s) {1..})) at_top"
    proof (rule contour_integral_uniform_limit)
      show "valid_path path" unfolding path_def by auto
      show "sequentially \<noteq> bot" by auto
    next
      fix t :: real
      show "\<parallel>vector_derivative path (at t)\<parallel> \<le> sqrt (4 * T\<^sup>2)"
        unfolding path_def by (auto simp add: legacy_Complex_simps)
    next
      from path_image_conv
      have *: "uniformly_convergent_on img_path (\<lambda>N s. \<Sum>n\<le>N. fds_nth f n / nat_power n s)"
        by (intro uniformly_convergent_eval_fds) (unfold path_def img_path_def, auto)
      have *: "uniformly_convergent_on img_path (\<lambda>N s. \<Sum>n = 1..N. a n / n nat_powr s)"
      proof -
        have "(\<Sum>n\<le>N. fds_nth f n / nat_power n s) = (\<Sum>n = 1..N. a n / n nat_powr s)" for N s
        proof -
          have "(\<Sum>n\<le>N. fds_nth f n / nat_power n s) = (\<Sum>n\<le>N. a n / n nat_powr s)"
            unfolding a_def nat_power_complex_def by auto
          also have "\<dots> = (\<Sum>n\<in>{..N} - {0}. a n / n nat_powr s)"
            by (subst sum_diff1) auto
          also have "\<dots> = (\<Sum>n = 1..N. a n / n nat_powr s)"
          proof -
            have "{..N} - {0} = {1..N}" by auto
            thus ?thesis by auto
          qed
          finally show ?thesis by auto
        qed
        thus ?thesis using * by auto
      qed
      hence "uniform_limit img_path
        (\<lambda>N s. \<Sum>n = 1..N. a n / n nat_powr s)
        (\<lambda>s. \<Sum>`n \<ge> 1. a n / n nat_powr s) at_top"
      proof -
        have "uniform_limit img_path
          (\<lambda>N s. \<Sum>n = 1..N. a n / n nat_powr s)
          (\<lambda>s. lim (\<lambda>N. \<Sum>n = 1..N. a n / n nat_powr s)) at_top"
          using * by (subst (asm) uniformly_convergent_uniform_limit_iff)
        moreover have "lim (\<lambda>N. \<Sum>n = 1..N. a n / n nat_powr s) = (\<Sum>`n \<ge> 1. a n / n nat_powr s)" for s
          by (rule subsum_ge_limit)
        ultimately show ?thesis by auto
      qed
      moreover have "bounded ((\<lambda>s. subsum (\<lambda>n. a n / n nat_powr s) {1..}) ` img_path)" (is "bounded ?A")
      proof -
        have "bounded (eval_fds f ` img_path)"
          by (intro compact_imp_bounded compact_continuous_image continuous_on_eval_fds)
             (use path_image_conv img_path_def path_def in auto)
        moreover have "\<dots> = ?A"
          unfolding a_def by (intro image_cong refl eval_fds_complex_subsum(1) converge_on_path)
        ultimately show ?thesis by auto
      qed
      moreover have "bounded ((\<lambda>s. x powr s / s) ` img_path)"
        unfolding img_path_def path_def
        by (intro compact_imp_bounded compact_continuous_image continuous_intros, auto)
           (use Hx in auto, use Hb in \<open>auto simp add: closed_segment_def legacy_Complex_simps algebra_simps\<close>)
      ultimately have "uniform_limit img_path
        (\<lambda>N s. (\<Sum>n = 1..N. a n / n nat_powr s) * (x powr s / s))
        (\<lambda>s. (\<Sum>`n \<ge> 1. a n / n nat_powr s) * (x powr s / s)) at_top" (is ?P)
        by (intro uniform_lim_mult uniform_limit_const)
      moreover have "?P = uniform_limit (path_image path)
        (\<lambda>N s. sum (h s) {1..N}) (\<lambda>s. subsum (h s) {1..}) at_top" (is "?P = ?Q")
        unfolding h_def
        by (fold img_path_def, rule uniform_limit_cong', subst sum_distrib_right [symmetric], rule refl)
           (subst subsum_mult2, intro summable_on_path, auto)
      ultimately show ?Q by blast
    next
      from h_integrable
      show "\<forall>\<^sub>F N in at_top. (\<lambda>s. sum (h s) {1..N}) contour_integrable_on path"
        unfolding h_def by (intro eventuallyI contour_integrable_sum) auto
    qed
    hence *: "has_subsum (\<lambda>n. contour_integral path (\<lambda>s. h s n)) {1..} (contour_integral path (\<lambda>s. subsum (h s) {1..}))"
      using h_integrable by (subst (asm) contour_integral_sum) (auto intro: has_subsum_ge_limit)
    case 1 from * show ?case unfolding h_def by (intro has_subsum_summable)
    case 2 from * show ?case unfolding h_def by (rule subsumI)
  qed
  note this(2) also have
    sum_2: "(\<lambda>n. a n * G n) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. a n * G n)"
  proof (goal_cases)
    have *: "a n * G n = contour_integral path (\<lambda>s. h s n)" when Hn: "n \<in> {1..}" for n :: nat
    proof -
      have "(\<lambda>s. (x / n) powr s / s) contour_integrable_on path"
        unfolding path_def by (rule perron_integrable) (use Hn Hx hT in auto)
      moreover have "contour_integral path (\<lambda>s. h s n) = contour_integral path (\<lambda>s. a n * ((x / n) powr s / s))"
      proof (intro contour_integral_cong refl)
        fix s :: complex
        have "(x / n) powr s * n powr s = ((x / n :: complex) * n) powr s"
          by (rule powr_times_real [symmetric]) (use Hn Hx in auto)
        also have "\<dots> = x powr s" using Hn by auto
        finally have "(x / n) powr s = x powr s / n powr s" using Hn by (intro eq_divide_imp) auto
        thus "h s n = a n * ((x / n) powr s / s)" unfolding h_def by (auto simp add: field_simps)
      qed
      ultimately show ?thesis unfolding G_def by (subst (asm) contour_integral_lmul) auto
    qed
    case 1 show ?case by (subst subsummable_cong) (use * sum_1 in auto)
    case 2 show ?case by (intro subsum_cong * [symmetric])
  qed
  note this(2) finally have
    "1 / (2 * pi * \<i>) * contour_integral path g = (\<Sum>`n \<ge> 1. a n * G n) * (1 / (2 * pi * \<i>))" by auto
  also have
    sum_3: "(\<lambda>n. a n * G n * (1 / (2 * pi * \<i>))) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. a n * G n * (1 / (2 * pi * \<i>)))"
    by (intro subsummable_mult2 subsum_mult2 [symmetric] sum_2)+
  note this(2) also have
    sum_4: "(\<lambda>n. a n * H n) subsummable {1..}"
    and "\<dots> = (\<Sum>`n \<ge> 1. a n * H n)"
    unfolding H_def using sum_3 by auto
  note this(2) also have
    "\<dots> - (\<Sum>`n \<ge> 1. if n \<le> x then a n else 0)
      = (\<Sum>`n \<ge> 1. a n * H n - (if n \<le> x then a n else 0))"
    using sum_4
    by (rule subsum_minus(1), unfold subsummable_def)
       (auto simp add: if_if_eq_conj nat_le_real_iff)
  moreover have "(\<Sum>`n \<ge> 1. if n \<le> x then a n else 0) = sum_upto a x"
  proof -
    have "(\<Sum>`n \<ge> 1. if n \<le> x then a n else 0) = (\<Sum>n :: nat|n \<in> {1..} \<and> n \<le> x. a n)"
      by (intro subsumI [symmetric] has_subsum_If_finite) (auto simp add: nat_le_real_iff)
    also have "\<dots> = sum_upto a x"
    proof -
      have "{n :: nat. n \<in> {1..} \<and> n \<le> x} = {n. 0 < n \<and> n \<le> x}" by auto
      thus ?thesis unfolding sum_upto_def by auto
    qed
    finally show ?thesis .
  qed
  moreover have "(\<Sum>`n \<ge> 1. a n * H n - (if n \<le> x then a n else 0)) = (\<Sum>`n \<ge> 1. a n * F' n)"
    unfolding F_def F'_def G_def H_def by (rule subsum_cong) (auto simp add: algebra_simps)
  ultimately have result: "\<parallel>sum_upto a x - 1 / (2 * pi * \<i>) * contour_integral path g\<parallel> = \<parallel>\<Sum>`n \<ge> 1. a n * F' n\<parallel>"
    by (subst norm_minus_commute) auto
  case 1 show ?case
  proof -
    have "closed_segment (Complex b (- T)) (Complex b T) \<subseteq> {s. conv_abscissa f < ereal (s \<bullet> 1)}"
      using path_image_conv unfolding img_path_def path_def by auto
    thus ?thesis unfolding path_def
      by (intro contour_integrable_continuous_linepath continuous_intros)
         (use Hx zero_notin_path in auto)
  qed
  case 2 show ?case using perron_bound result unfolding g_def by linarith
qed
end

theorem perron_formula:
  fixes b B H T x :: real and f :: "complex fds"
  assumes Hb: "0 < b" and hT: "b \<le> T"
    and Hb': "abs_conv_abscissa f < b"
    and hH: "2 \<le> H" and hH': "b + 1 \<le> H" and Hx: "2 \<le> x"
    and hB: "(\<Sum>`n \<ge> 1. \<parallel>fds_nth f n\<parallel> / n nat_powr b) \<le> B"
  shows "(\<lambda>s. eval_fds f s * x powr s / s) contour_integrable_on (linepath (Complex b (-T)) (Complex b T))"
        "\<parallel>sum_upto (fds_nth f) x - 1 / (2 * pi * \<i>) *
          contour_integral (linepath (Complex b (-T)) (Complex b T)) (\<lambda>s. eval_fds f s * x powr s / s)\<parallel>
         \<le> x powr b * H * B / T + 3 * (2 + ln (T / b)) * (\<Sum>n | x - x / H \<le> n \<and> n \<le> x + x / H. \<parallel>fds_nth f n\<parallel>)"
proof (goal_cases)
  interpret z: perron_locale using assms unfolding perron_locale_def by auto
  case 1 show ?case using z.perron(1) unfolding z.path_def .
  case 2 show ?case using z.perron(2) unfolding z.path_def z.region_def z.a_def .
qed

unbundle no_pnt_notation

section \<open>Estimation of the order of $\frac{\zeta'(s)}{\zeta(s)}$\<close>

unbundle "pnt_notation"
notation primes_psi ("\<psi>")

lemma eventually_le_imp_bigo:
  assumes "\<forall>\<^sub>F x in F. \<parallel>f x\<parallel> \<le> g x"
  shows "f \<in> O[F](g)"
proof -
  from assms have "\<forall>\<^sub>F x in F. \<parallel>f x\<parallel> \<le> 1 * \<parallel>g x\<parallel>" by eventually_elim auto
  thus ?thesis by (rule bigoI)
qed

lemma eventually_le_imp_bigo':
  assumes "\<forall>\<^sub>F x in F. \<parallel>f x\<parallel> \<le> g x"
  shows "(\<lambda>x. \<parallel>f x\<parallel>) \<in> O[F](g)"
proof -
  from assms have "\<forall>\<^sub>F x in F. \<parallel>\<parallel>f x\<parallel>\<parallel> \<le> 1 * \<parallel>g x\<parallel>"
    by eventually_elim auto
  thus ?thesis by (rule bigoI)
qed

lemma le_imp_bigo:
  assumes "\<And>x. \<parallel>f x\<parallel> \<le> g x"
  shows "f \<in> O[F](g)"
  by (intro eventually_le_imp_bigo eventuallyI assms)

lemma le_imp_bigo':
  assumes "\<And>x. \<parallel>f x\<parallel> \<le> g x"
  shows "(\<lambda>x. \<parallel>f x\<parallel>) \<in> O[F](g)"
  by (intro eventually_le_imp_bigo' eventuallyI assms)

lemma zeta_div_bound':
  assumes "1 + exp (- 5 * ln (17 + 4 * t)) \<le> \<sigma>"
    and "13 / 22 \<le> t"
    and "z \<in> cball (Complex \<sigma> t) (1 / 2)"
  shows "\<parallel>zeta z / zeta (Complex \<sigma> t)\<parallel> \<le> exp (15 * ln (17 + 4 * t))"
proof -
  interpret z: zeta_bound_param_2
    "\<lambda>t. 1 / 2" "\<lambda>t. if 0 \<le> t then 5 * ln (15 + 2 * t) else 5 * ln 15" t \<sigma> t
    unfolding zeta_bound_param_1_def zeta_bound_param_2_def
              zeta_bound_param_1_axioms_def zeta_bound_param_2_axioms_def
    by (safe, rule zeta_bound_params.zeta_bound_param_axioms)
       (use assms in auto)
  show ?thesis using z.zeta_div_bound assms(2) assms(3)
    unfolding z.s_def z.r_def by auto
qed

lemma zeta_div_bound:
  assumes "1 + exp (- 5 * ln (17 + 4 * \<bar>t\<bar>)) \<le> \<sigma>"
    and "13 / 22 \<le> \<bar>t\<bar>"
    and "z \<in> cball (Complex \<sigma> t) (1 / 2)"
  shows "\<parallel>zeta z / zeta (Complex \<sigma> t)\<parallel> \<le> exp (15 * ln (17 + 4 * \<bar>t\<bar>))"
proof (cases "0 \<le> t")
  case True with assms(2) have "13 / 22 \<le> t" by auto
  thus ?thesis using assms by (auto intro: zeta_div_bound')
next
  case False with assms(2) have Ht: "t \<le> - 13 / 22" by auto
  moreover have 1: "Complex \<sigma> (- t) = cnj (Complex \<sigma> t)" by (auto simp add: legacy_Complex_simps)
  ultimately have "\<parallel>zeta (cnj z) / zeta (Complex \<sigma> (- t))\<parallel> \<le> exp (15 * ln (17 + 4 * (- t)))"
    using assms(1) assms(3)
    by (intro zeta_div_bound', auto simp add: dist_complex_def)
       (subst complex_cnj_diff [symmetric], subst complex_mod_cnj)
  thus ?thesis using Ht by (subst (asm) 1) (simp add: norm_divide)
qed

definition C\<^sub>2 where "C\<^sub>2 \<equiv> 781200000 :: real"
lemma C\<^sub>1_gt_zero: "0 < C\<^sub>1" unfolding C\<^sub>1_def by auto
lemma C\<^sub>2_gt_zero: "0 < C\<^sub>2" unfolding C\<^sub>2_def by auto

lemma logderiv_zeta_order_estimate':
"\<forall>\<^sub>F t in (abs going_to at_top).
  \<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
  \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
proof -
  define F where "F :: real filter \<equiv> abs going_to at_top"
  define r where "r t \<equiv> C\<^sub>1 / ln (\<bar>t\<bar> + 3)" for t :: real
  define s where "s \<sigma> t \<equiv> Complex (\<sigma> + 2 / 7 * r t) t" for \<sigma> t
  have r_nonneg: "0 \<le> r t" for t unfolding C\<^sub>1_def r_def by auto
  have "\<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
    when h: "1 - 1 / 7 * r t \<le> \<sigma>"
            "exp (- 5 * ln (17 + 4 * \<bar>t\<bar>)) \<le> 1 / 7 * r t"
            "8 / 7 * r t \<le> \<bar>t\<bar>"
            "8 / 7 * r t \<le> 1 / 2"
            "13 / 22 \<le> \<bar>t\<bar>" for \<sigma> t
  proof -
    have "\<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> 8 * (15 * ln (17 + 4 * \<bar>t\<bar>)) / (8 / 7 * r t)"
    proof (rule lemma_3_9_beta1' [where ?s = "s \<sigma> t"], goal_cases)
      case 1 show ?case unfolding C\<^sub>1_def r_def by auto
      case 2 show ?case by auto
      have notin_ball: "1 \<notin> ball (s \<sigma> t) (8 / 7 * r t)"
      proof -
        note h(3)
        also have "\<bar>t\<bar> = \<bar>Im (Complex (\<sigma> + 2 / 7 * r t) t - 1)\<bar>" by auto
        also have "\<dots> \<le> \<parallel>Complex (\<sigma> + 2 / 7 * r t) t - 1\<parallel>" by (rule abs_Im_le_cmod)
        finally show ?thesis
          unfolding s_def by (auto simp add: dist_complex_def)
      qed
      case 3 show ?case by (intro holomorphic_zeta notin_ball)
      case 6 show ?case
        using r_nonneg unfolding s_def
        by (auto simp add: dist_complex_def legacy_Complex_simps)
      fix z assume Hz: "z \<in> ball (s \<sigma> t) (8 / 7 * r t)"
      show "zeta z \<noteq> 0"
      proof (rule ccontr)
        assume "\<not> zeta z \<noteq> 0"
        hence zero: "zeta (Complex (Re z) (Im z)) = 0" by auto
        have "r t \<le> C\<^sub>1 / ln (\<bar>Im z\<bar> + 2)"
        proof -
          have "\<parallel>s \<sigma> t - z\<parallel> < 1"
            using Hz h(4) by (auto simp add: dist_complex_def)
          hence "\<bar>t - Im z\<bar> < 1"
            using abs_Im_le_cmod [of "s \<sigma> t - z"]
            unfolding s_def by (auto simp add: legacy_Complex_simps)
          hence "\<bar>Im z\<bar> < \<bar>t\<bar> + 1" by auto
          thus ?thesis unfolding r_def
            by (intro divide_left_mono mult_pos_pos)
               (subst ln_le_cancel_iff, use C\<^sub>1_gt_zero in auto)
        qed
        also have "\<dots> \<le> 1 - Re z"
          using notin_ball Hz by (intro zeta_nonzero_region zero) auto
        also have "\<dots> < 1 - Re (s \<sigma> t) + 8 / 7 * r t"
        proof -
          have "Re (s \<sigma> t - z) \<le> \<bar>Re (s \<sigma> t - z)\<bar>" by auto
          also have "\<dots> < 8 / 7 * r t"
            using Hz abs_Re_le_cmod [of "s \<sigma> t - z"]
            by (auto simp add: dist_complex_def)
          ultimately show ?thesis by auto
        qed
        also have "\<dots> = 1 - \<sigma> + 6 / 7 * r t" unfolding s_def by auto
        also have "\<dots> \<le> r t" using h(1) by auto
        finally show False by auto
      qed
      from Hz have "z \<in> cball (s \<sigma> t) (1 / 2)"
        using h(4) by auto
      thus "\<parallel>zeta z / zeta (s \<sigma> t)\<parallel> \<le> exp (15 * ln (17 + 4 * \<bar>t\<bar>))"
        using h(1) h(2) unfolding s_def
        by (intro zeta_div_bound h(5)) auto
    qed
    also have "\<dots> = 105 / r t * ln (17 + 4 * \<bar>t\<bar>)"
      by (auto simp add: field_simps)
    also have "\<dots> \<le> 525 / C\<^sub>1 * ln (\<bar>t\<bar> + 2) * ln (\<bar>t\<bar> + 3)"
    proof -
      have "105 / r t * ln (17 + 4 * \<bar>t\<bar>) \<le> 105 / r t * (5 * ln (\<bar>t\<bar> + 2))"
        using r_nonneg by (intro mult_left_mono mult_right_mono ln_bound_1) auto
      thus ?thesis unfolding r_def by (simp add: mult_ac)
    qed
    also have "\<dots> \<le> 525 / C\<^sub>1 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
      unfolding power2_eq_square
      by (simp add: mult_ac, intro divide_right_mono mult_right_mono)
         (subst ln_le_cancel_iff, use C\<^sub>1_gt_zero in auto)
    also have "\<dots> = C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2" unfolding C\<^sub>1_def C\<^sub>2_def by auto
    finally show ?thesis .
  qed
  hence
    "\<forall>\<^sub>F t in F.
        exp (- 5 * ln (17 + 4 * \<bar>t\<bar>)) \<le> 1 / 7 * r t
    \<longrightarrow> 8 / 7 * r t \<le> \<bar>t\<bar>
    \<longrightarrow> 8 / 7 * r t \<le> 1 / 2
    \<longrightarrow> 13 / 22 \<le> \<bar>t\<bar>
    \<longrightarrow> (\<forall>\<sigma>. 1 - 1 / 7 * r t \<le> \<sigma>
      \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2)"
    by (rule_tac eventuallyI) blast
  moreover have "\<forall>\<^sub>F t in F. exp (- 5 * ln (17 + 4 * \<bar>t\<bar>)) \<le> 1 / 7 * r t"
    unfolding F_def r_def C\<^sub>1_def by (rule eventually_going_toI) real_asymp
  moreover have "\<forall>\<^sub>F t in F. 8 / 7 * r t \<le> \<bar>t\<bar>"
    unfolding F_def r_def C\<^sub>1_def by (rule eventually_going_toI) real_asymp
  moreover have "\<forall>\<^sub>F t in F. 8 / 7 * r t \<le> 1 / 2"
    unfolding F_def r_def C\<^sub>1_def by (rule eventually_going_toI) real_asymp
  moreover have "\<forall>\<^sub>F t in F. 13 / 22 \<le> \<bar>t\<bar>"
    unfolding F_def by (rule eventually_going_toI) real_asymp
  ultimately have
    "\<forall>\<^sub>F t in F. (\<forall>\<sigma>. 1 - 1 / 7 * r t \<le> \<sigma>
      \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2)"
    by eventually_elim blast
  thus ?thesis unfolding F_def r_def by auto
qed

definition C\<^sub>3 where
"C\<^sub>3 \<equiv> SOME T. 0 < T \<and>
  (\<forall>t. T \<le> \<bar>t\<bar> \<longrightarrow>
    (\<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
     \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2))"

lemma C\<^sub>3_prop:
  "0 < C\<^sub>3 \<and>
  (\<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<longrightarrow>
    (\<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
    \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2))"
proof -
  obtain T' where hT:
  "\<And>t. T' \<le> \<bar>t\<bar> \<Longrightarrow>
    (\<forall>\<sigma>. 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>
     \<longrightarrow> \<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2)"
    using logderiv_zeta_order_estimate'
      [unfolded going_to_def, THEN rev_iffD1,
      OF eventually_filtercomap_at_top_linorder] by blast
  define T where "T \<equiv> max 1 T'"
  show ?thesis unfolding C\<^sub>3_def
    by (rule someI [of _ T]) (unfold T_def, use hT in auto)
qed

lemma C\<^sub>3_gt_zero: "0 < C\<^sub>3" using C\<^sub>3_prop by blast

theorem logderiv_zeta_order_estimate:
  assumes "1 - 1 / 7 * C\<^sub>1 / ln (\<bar>t\<bar> + 3) \<le> \<sigma>" "C\<^sub>3 \<le> \<bar>t\<bar>"
  shows "\<parallel>logderiv zeta (Complex \<sigma> t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>t\<bar> + 3))\<^sup>2"
  using assms C\<^sub>3_prop by blast

definition zeta' where "zeta' s \<equiv> pre_zeta 1 s * (s - 1) + 1"

lemma zeta'_analytic:
  "zeta' analytic_on UNIV"
  unfolding zeta'_def by (intro analytic_intros) auto

lemma zeta'_analytic_on [analytic_intros]:
  "zeta' analytic_on A" using zeta'_analytic analytic_on_subset by auto

lemma zeta'_holomorphic_on [holomorphic_intros]:
  "zeta' holomorphic_on A" using zeta'_analytic_on by (intro analytic_imp_holomorphic)

lemma zeta_eq_zeta':
  "zeta s = zeta' s / (s - 1)"
proof (cases "s = 1")
  case True thus ?thesis using zeta_1 unfolding zeta'_def by auto
next
  case False with zeta_pole_eq [OF this]
  show ?thesis unfolding zeta'_def by (auto simp add: field_simps)
qed

lemma zeta'_1 [simp]: "zeta' 1 = 1" unfolding zeta'_def by auto

lemma zeta_eq_zero_iff_zeta':
  shows "s \<noteq> 1 \<Longrightarrow> zeta' s = 0 \<longleftrightarrow> zeta s = 0"
  using zeta_eq_zeta' [of s] by auto

lemma zeta'_eq_zero_iff:
  shows "zeta' s = 0 \<longleftrightarrow> zeta s = 0 \<and> s \<noteq> 1"
  by (cases "s = 1", use zeta_eq_zero_iff_zeta' in auto)

lemma zeta_eq_zero_iff:
  shows "zeta s = 0 \<longleftrightarrow> zeta' s = 0 \<or> s = 1"
  by (subst zeta'_eq_zero_iff, use zeta_1 in auto)

lemma logderiv_inverse:
  assumes "x \<noteq> 0"
  shows "logderiv (\<lambda>x. 1 / x) x = - 1 / x"
proof -
  have "deriv (\<lambda>x. 1 / x) x = (deriv (\<lambda>x. 1) x * x - 1 * deriv (\<lambda>x. x) x) / x\<^sup>2"
    by (rule deriv_divide) (use assms in auto)
  hence "deriv (\<lambda>x. 1 / x) x = - 1 / x\<^sup>2" by auto
  thus ?thesis unfolding logderiv_def power2_eq_square using assms by auto
qed

lemma logderiv_zeta_eq_zeta':
  assumes "s \<noteq> 1" "zeta s \<noteq> 0"
  shows "logderiv zeta s = logderiv zeta' s - 1 / (s - 1)"
proof -
  have "logderiv zeta s = logderiv (\<lambda>s. zeta' s * (1 / (s - 1))) s"
    using zeta_eq_zeta' by auto metis
  also have "\<dots> = logderiv zeta' s + logderiv (\<lambda>s. 1 / (s - 1)) s"
  proof -
    have "zeta' s \<noteq> 0" using assms zeta_eq_zero_iff_zeta' by auto
    hence "zeta' log_differentiable s"
      unfolding log_differentiable_def
      by (intro conjI analytic_on_imp_differentiable_at)
         (rule zeta'_analytic, auto)
    moreover have "(\<lambda>z. 1 / (z - 1)) log_differentiable s"
      unfolding log_differentiable_def using assms(1)
      by (intro derivative_intros conjI, auto)
    ultimately show ?thesis using assms by (intro logderiv_mult(1))
  qed
  also have "logderiv (\<lambda>s. 1 / (- 1 + s)) s = logderiv (\<lambda>s. 1 / s) (- 1 + s)"
    by (rule logderiv_shift) (insert assms(1), auto intro: derivative_intros)
  moreover have "\<dots> = - 1 / (- 1 + s)"
    by (rule logderiv_inverse) (use assms(1) in auto)
  ultimately show ?thesis by auto
qed

theorem analytic_logderiv [analytic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0"
  shows "(\<lambda>s. logderiv f s) analytic_on A"
  using assms unfolding logderiv_def by (intro analytic_intros)

definition zeta_zerofree_region
  where "zeta_zerofree_region \<equiv> {s. s \<noteq> 1 \<and> 1 - C\<^sub>1 / ln (\<bar>Im s\<bar> + 2) < Re s}"
definition logderiv_zeta_region
  where "logderiv_zeta_region \<equiv> {s. C\<^sub>3 \<le> \<bar>Im s\<bar> \<and> 1 - 1 / 7 * C\<^sub>1 / ln (\<bar>Im s\<bar> + 3) \<le> Re s}"
definition zeta_strip_region
  where "zeta_strip_region \<sigma> T \<equiv> {s. s \<noteq> 1 \<and> \<sigma> \<le> Re s \<and> \<bar>Im s\<bar> \<le> T}"
definition zeta_strip_region'
  where "zeta_strip_region' \<sigma> T \<equiv> {s. s \<noteq> 1 \<and> \<sigma> \<le> Re s \<and> C\<^sub>3 \<le> \<bar>Im s\<bar> \<and> \<bar>Im s\<bar> \<le> T}"

theorem strip_in_zerofree_region:
  assumes "1 - C\<^sub>1 / ln (T + 2) < \<sigma>"
  shows "zeta_strip_region \<sigma> T \<subseteq> zeta_zerofree_region"
proof
  fix s assume Hs: "s \<in> zeta_strip_region \<sigma> T"
  hence Hs': "s \<noteq> 1" "\<sigma> \<le> Re s" "\<bar>Im s\<bar> \<le> T" unfolding zeta_strip_region_def by auto
  from this(3) have "C\<^sub>1 / ln (T + 2) \<le> C\<^sub>1 / ln (\<bar>Im s\<bar> + 2)"
    using C\<^sub>1_gt_zero by (intro divide_left_mono mult_pos_pos) auto
  thus "s \<in> zeta_zerofree_region" using Hs' assms unfolding zeta_zerofree_region_def by auto
qed

theorem strip_in_logderiv_zeta_region:
  assumes "1 - 1 / 7 * C\<^sub>1 / ln (T + 3) \<le> \<sigma>"
  shows "zeta_strip_region' \<sigma> T \<subseteq> logderiv_zeta_region"
proof
  fix s assume Hs: "s \<in> zeta_strip_region' \<sigma> T"
  hence Hs': "s \<noteq> 1" "\<sigma> \<le> Re s" "C\<^sub>3 \<le> \<bar>Im s\<bar>" "\<bar>Im s\<bar> \<le> T" unfolding zeta_strip_region'_def by auto
  from this(4) have "C\<^sub>1 / (7 * ln (T + 3)) \<le> C\<^sub>1 / (7 * ln (\<bar>Im s\<bar> + 3))"
    using C\<^sub>1_gt_zero by (intro divide_left_mono mult_pos_pos) auto
  thus "s \<in> logderiv_zeta_region" using Hs' assms unfolding logderiv_zeta_region_def by auto
qed

theorem strip_condition_imp:
  assumes "0 \<le> T" "1 - 1 / 7 * C\<^sub>1 / ln (T + 3) \<le> \<sigma>"
  shows "1 - C\<^sub>1 / ln (T + 2) < \<sigma>"
proof -
  have "ln (T + 2) \<le> 7 * ln (T + 2)" using assms(1) by auto
  also have "\<dots> < 7 * ln (T + 3)" using assms(1) by auto
  finally have "C\<^sub>1 / (7 * ln (T + 3)) < C\<^sub>1 / ln (T + 2)"
    using C\<^sub>1_gt_zero assms(1) by (intro divide_strict_left_mono mult_pos_pos) auto
  thus ?thesis using assms(2) by auto
qed

theorem zeta_zerofree_region:
  assumes "s \<in> zeta_zerofree_region"
  shows "zeta s \<noteq> 0"
  using zeta_nonzero_region [of "Re s" "Im s"] assms
  unfolding zeta_zerofree_region_def by auto

theorem logderiv_zeta_region_estimate:
  assumes "s \<in> logderiv_zeta_region"
  shows "\<parallel>logderiv zeta s\<parallel> \<le> C\<^sub>2 * (ln (\<bar>Im s\<bar> + 3))\<^sup>2"
  using logderiv_zeta_order_estimate [of "Im s" "Re s"] assms
  unfolding logderiv_zeta_region_def by auto

definition C\<^sub>4 :: real where "C\<^sub>4 \<equiv> 1 / 10416001"
lemma C\<^sub>4_prop:
  "\<forall>\<^sub>F x in at_top. C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))"
  unfolding C\<^sub>1_def C\<^sub>4_def by real_asymp

lemma C\<^sub>4_gt_zero: "0 < C\<^sub>4" unfolding C\<^sub>4_def by auto

definition C\<^sub>5_prop where
"C\<^sub>5_prop C\<^sub>5 \<equiv>
  0 < C\<^sub>5 \<and> (\<forall>\<^sub>F x in at_top. (\<forall>t. \<bar>t\<bar> \<le> x
    \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2))"

lemma logderiv_zeta_bound_vertical':
  "\<exists>C\<^sub>5. C\<^sub>5_prop C\<^sub>5"
proof -
  define K where "K \<equiv> cbox (Complex 0 (-C\<^sub>3)) (Complex 2 C\<^sub>3)"
  define \<Gamma> where "\<Gamma> \<equiv> {s \<in> K. zeta' s = 0}"
  have "zeta' not_zero_on K"
    unfolding not_zero_on_def K_def using C\<^sub>3_gt_zero
    by (intro bexI [where x = 2])
       (auto simp add: zeta_eq_zero_iff_zeta' zeta_2 in_cbox_complex_iff)
  hence fin: "finite \<Gamma>"
    unfolding \<Gamma>_def K_def
    by (auto intro!: convex_connected analytic_compact_finite_zeros zeta'_analytic)
  define \<alpha> where "\<alpha> \<equiv> if \<Gamma> = {} then 0 else (1 + Max (Re ` \<Gamma>)) / 2"
  define K' where "K' \<equiv> cbox (Complex \<alpha> (-C\<^sub>3)) (Complex 1 C\<^sub>3)"
  have H\<alpha>: "\<alpha> \<in> {0..<1}"
  proof (cases "\<Gamma> = {}")
    case True thus ?thesis unfolding \<alpha>_def by auto
  next
    case False hence h\<Gamma>: "\<Gamma> \<noteq> {}" .
    moreover have "Re a < 1" if Ha: "a \<in> \<Gamma>" for a
    proof (rule ccontr)
      assume "\<not> Re a < 1" hence "1 \<le> Re a" by auto
      hence "zeta' a \<noteq> 0" by (subst zeta'_eq_zero_iff) (use zeta_Re_ge_1_nonzero in auto)
      thus False using Ha unfolding \<Gamma>_def by auto
    qed
    moreover have "\<exists>a\<in>\<Gamma>. 0 \<le> Re a"
    proof -
      from h\<Gamma> have "\<exists>a. a \<in> \<Gamma>" by auto
      moreover have "\<And>a. a \<in> \<Gamma> \<Longrightarrow> 0 \<le> Re a"
        unfolding \<Gamma>_def K_def by (auto simp add: in_cbox_complex_iff)
      ultimately show ?thesis by auto
    qed
    ultimately have "0 \<le> Max (Re ` \<Gamma>)" "Max (Re ` \<Gamma>) < 1"
      using fin by (auto simp add: Max_ge_iff)
    thus ?thesis unfolding \<alpha>_def using h\<Gamma> by auto
  qed
  have nonzero: "zeta' z \<noteq> 0" when "z \<in> K'" for z
  proof (rule ccontr)
    assume "\<not> zeta' z \<noteq> 0"
    moreover have "K' \<subseteq> K" unfolding K'_def K_def
      by (rule subset_box_imp) (insert H\<alpha>, simp add: Basis_complex_def)
    ultimately have Hz: "z \<in> \<Gamma>" unfolding \<Gamma>_def using that by auto
    hence "Re z \<le> Max (Re ` \<Gamma>)" using fin by (intro Max_ge) auto
    also have "\<dots> < \<alpha>"
    proof -
      from Hz have "\<Gamma> \<noteq> {}" by auto
      thus ?thesis using H\<alpha> unfolding \<alpha>_def by auto
    qed
    finally have "Re z < \<alpha>" .
    moreover from \<open>z \<in> K'\<close> have "\<alpha> \<le> Re z"
      unfolding K'_def by (simp add: in_cbox_complex_iff)
    ultimately show False by auto
  qed
  hence "logderiv zeta' analytic_on K'" by (intro analytic_intros)
  moreover have "compact K'" unfolding K'_def by auto
  ultimately have "bounded ((logderiv zeta') ` K')"
    by (intro analytic_imp_holomorphic holomorphic_on_imp_continuous_on
        compact_imp_bounded compact_continuous_image)
  from this [THEN rev_iffD1, OF bounded_pos]
  obtain M where
    hM: "\<And>s. s \<in> K' \<Longrightarrow> \<parallel>logderiv zeta' s\<parallel> \<le> M" by auto
  have "(\<lambda>t. C\<^sub>2 * (ln (t + 3))\<^sup>2) \<in> O(\<lambda>x. (ln x)\<^sup>2)" using C\<^sub>2_gt_zero by real_asymp
  then obtain \<gamma> where
    H\<gamma>: "\<forall>\<^sub>F x in at_top. \<parallel>C\<^sub>2 * (ln (x + 3))\<^sup>2\<parallel> \<le> \<gamma> * \<parallel>(ln x)\<^sup>2\<parallel>"
    unfolding bigo_def by auto
  define C\<^sub>5 where "C\<^sub>5 \<equiv> max 1 \<gamma>"
  have C\<^sub>5_gt_zero: "0 < C\<^sub>5" unfolding C\<^sub>5_def by auto
  have "\<forall>\<^sub>F x in at_top. \<gamma> * (ln x)\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2"
    by (intro eventuallyI mult_right_mono) (unfold C\<^sub>5_def, auto)
  with H\<gamma> have hC\<^sub>5: "\<forall>\<^sub>F x in at_top. C\<^sub>2 * (ln (x + 3))\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2"
    by eventually_elim (use C\<^sub>2_gt_zero in auto)
  have "\<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2"
    when h: "C\<^sub>3 \<le> \<bar>t\<bar>" "\<bar>t\<bar> \<le> x" "1 < x"
            "C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))"
            "C\<^sub>2 * (ln (x + 3))\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2" for x t
  proof -
    have "Re (Complex (1 - C\<^sub>4 / ln x) t) \<noteq> Re 1" using C\<^sub>4_gt_zero h(3) by auto
    hence "Complex (1 - C\<^sub>4 / ln x) t \<noteq> 1" by metis
    hence "Complex (1 - C\<^sub>4 / ln x) t \<in> zeta_strip_region' (1 - C\<^sub>4 / ln x) x"
      unfolding zeta_strip_region'_def using h(1) h(2) by auto
    hence "\<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>2 * (ln (\<bar>Im (Complex (1 - C\<^sub>4 / ln x) t)\<bar> + 3))\<^sup>2"
      by (intro logderiv_zeta_region_estimate, rule_tac set_mp)
         (rule strip_in_logderiv_zeta_region [where ?\<sigma> = "1 - C\<^sub>4 / ln x" and ?T = x], use h(4) in auto)
    also have "\<dots> \<le> C\<^sub>2 * (ln (x + 3))\<^sup>2"
      by (intro mult_left_mono, subst power2_le_iff_abs_le)
         (use C\<^sub>2_gt_zero h(2) h(3) in auto)
    also have "\<dots> \<le> C\<^sub>5 * (ln x)\<^sup>2" by (rule h(5))
    finally show ?thesis .
  qed
  hence "\<forall>\<^sub>F x in at_top. \<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<longrightarrow> \<bar>t\<bar> \<le> x
    \<longrightarrow> 1 < x \<longrightarrow> C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))
    \<longrightarrow> C\<^sub>2 * (ln (x + 3))\<^sup>2 \<le> C\<^sub>5 * (ln x)\<^sup>2
    \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2"
    by (intro eventuallyI) blast
  moreover have "\<forall>\<^sub>F x in at_top. (1 :: real) < x" by auto
  ultimately have 1: "\<forall>\<^sub>F x in at_top. \<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<longrightarrow> \<bar>t\<bar> \<le> x
    \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2"
    using C\<^sub>4_prop hC\<^sub>5 by eventually_elim blast
  define f where "f x \<equiv> 1 - C\<^sub>4 / ln x" for x
  define g where "g x t \<equiv> Complex (f x) t" for x t
  let ?P = "\<lambda>x t. \<parallel>logderiv zeta (g x t)\<parallel> \<le> M + ln x / C\<^sub>4"
  have "\<alpha> < 1" using H\<alpha> by auto
  hence "\<forall>\<^sub>F x in at_top. \<alpha> \<le> f x" unfolding f_def using C\<^sub>4_gt_zero by real_asymp
  moreover have f_lt_1: "\<forall>\<^sub>F x in at_top. f x < 1" unfolding f_def using C\<^sub>4_gt_zero by real_asymp
  ultimately have "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> g x t \<in> K' - {1}"
    unfolding g_def K'_def by eventually_elim (auto simp add: in_cbox_complex_iff legacy_Complex_simps)
  moreover have "\<parallel>logderiv zeta (g x t)\<parallel> \<le> M + 1 / (1 - f x)"
    when h: "g x t \<in> K' - {1}" "f x < 1" for x t
  proof -
    from h(1) have ne_1: "g x t \<noteq> 1" by auto
    hence "\<parallel>logderiv zeta (g x t)\<parallel> = \<parallel>logderiv zeta' (g x t) - 1 / (g x t - 1)\<parallel>"
      using h(1) nonzero
      by (subst logderiv_zeta_eq_zeta')
         (auto simp add: zeta_eq_zero_iff_zeta' [symmetric])
    also have "\<dots> \<le> \<parallel>logderiv zeta' (g x t)\<parallel> + \<parallel>1 / (g x t - 1)\<parallel>" by (rule norm_triangle_ineq4)
    also have "\<dots> \<le> M + 1 / (1 - f x)"
    proof -
      have "\<parallel>logderiv zeta' (g x t)\<parallel> \<le> M" using that by (auto intro: hM)
      moreover have "\<bar>Re (g x t - 1)\<bar> \<le> \<parallel>g x t - 1\<parallel>" by (rule abs_Re_le_cmod)
      hence "\<parallel>1 / (g x t - 1)\<parallel> \<le> 1 / (1 - f x)"
        using ne_1 h(2)
        by (auto simp add: norm_divide g_def
                 intro!: divide_left_mono mult_pos_pos)
      ultimately show ?thesis by auto
    qed
    finally show ?thesis .
  qed
  hence "\<forall>\<^sub>F x in at_top. \<forall>t. f x < 1
    \<longrightarrow> g x t \<in> K' - {1} 
    \<longrightarrow> \<parallel>logderiv zeta (g x t)\<parallel> \<le> M + 1 / (1 - f x)" by auto
  ultimately have "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> \<parallel>logderiv zeta (g x t)\<parallel> \<le> M + 1 / (1 - f x)"
    using f_lt_1 by eventually_elim blast
  hence "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> \<parallel>logderiv zeta (g x t)\<parallel> \<le> M + ln x / C\<^sub>4" unfolding f_def by auto
  moreover have "\<forall>\<^sub>F x in at_top. M + ln x / C\<^sub>4 \<le> C\<^sub>5 * (ln x)\<^sup>2" using C\<^sub>4_gt_zero C\<^sub>5_gt_zero by real_asymp
  ultimately have 2: "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> C\<^sub>3 \<longrightarrow> \<parallel>logderiv zeta (g x t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2" by eventually_elim auto
  show ?thesis
  proof (unfold C\<^sub>5_prop_def, intro exI conjI)
    show "0 < C\<^sub>5" by (rule C\<^sub>5_gt_zero)+
    have "\<forall>\<^sub>F x in at_top. \<forall>t. C\<^sub>3 \<le> \<bar>t\<bar> \<or> \<bar>t\<bar> \<le> C\<^sub>3"
      by (rule eventuallyI) auto
    with 1 2 show "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> x \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2"
      unfolding f_def g_def by eventually_elim blast
  qed
qed

definition C\<^sub>5 where "C\<^sub>5 \<equiv> SOME C\<^sub>5. C\<^sub>5_prop C\<^sub>5"

theorem
  C\<^sub>5_gt_zero: "0 < C\<^sub>5" (is ?prop_1) and
  logderiv_zeta_bound_vertical:
    "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> x
      \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln x) t)\<parallel> \<le> C\<^sub>5 * (ln x)\<^sup>2" (is ?prop_2)
proof -
  have "C\<^sub>5_prop C\<^sub>5" unfolding C\<^sub>5_def
    by (rule someI_ex) (rule logderiv_zeta_bound_vertical')
  thus ?prop_1 ?prop_2 unfolding C\<^sub>5_prop_def by auto
qed

section \<open>Deducing prime number theorem using Perron's formula\<close>

theorem has_sum_imp_has_subsum:
  fixes x :: "'a :: {comm_monoid_add, t2_space}"
  assumes "(f has_sum x) A"
  shows "has_subsum f A x"
proof -
  have "(\<forall>\<^sub>F x in at_top. sum f ({..<x} \<inter> A) \<in> S)"
    when "open S" "x \<in> S" for S
  proof -
    have "\<forall>S. open S \<longrightarrow> x \<in> S \<longrightarrow> (\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x \<in> S)"
      using assms unfolding has_sum_def tendsto_def .
    hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x \<in> S" using that by auto
    then obtain X where hX: "finite X" "X \<subseteq> A"
      and hY: "\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> sum f Y \<in> S"
      unfolding eventually_finite_subsets_at_top by metis
    define n where "n \<equiv> Max X + 1"
    show ?thesis
    proof (subst eventually_sequentially, standard, safe)
      fix m assume Hm: "n \<le> m"
      moreover have "x \<in> X \<Longrightarrow> x < n" for x
        unfolding n_def using Max_ge [OF hX(1), of x] by auto
      ultimately show "sum f ({..<m} \<inter> A) \<in> S"
        using hX(2) by (intro hY, auto) (metis order.strict_trans2)
    qed
  qed
  thus ?thesis unfolding has_subsum_def sums_def tendsto_def
    by (simp add: sum.inter_restrict [symmetric])
qed

lemma nat_le_self: "0 \<le> x \<Longrightarrow> nat (int x) \<le> x" by auto
lemma floor_le: "\<And>x :: real. \<lfloor>x\<rfloor> \<le> x" by auto
lemma ceil_ge: "\<And>x :: real. x \<le> \<lceil>x\<rceil>" by auto

lemma norm_fds_mangoldt_complex:
  "\<And>n. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel> = mangoldt_real n" by (simp add: fds_nth_fds)

lemma analytic_on_powr_right [analytic_intros]:
  assumes "f analytic_on s"
  shows "(\<lambda>z. w powr f z) analytic_on s"
proof (cases "w = 0")
  case False
  with assms show ?thesis
    unfolding analytic_on_def holomorphic_on_def field_differentiable_def
    by (metis (full_types) DERIV_chain' has_field_derivative_powr_right)
qed simp

lemma ln_ln_asymp_pos: "\<forall>\<^sub>F x :: real in at_top. 0 < ln (ln x)" by real_asymp
lemma ln_asymp_pos: "\<forall>\<^sub>F x :: real in at_top. 0 < ln x" by real_asymp
lemma x_asymp_pos: "\<forall>\<^sub>F x :: real in at_top. 0 < x" by auto

locale prime_number_theorem =
  fixes c \<epsilon> :: real
  assumes Hc: "0 < c" and Hc': "c * c < 2 * C\<^sub>4" and H\<epsilon>: "0 < \<epsilon>" "2 * \<epsilon> < c"
begin
notation primes_psi ("\<psi>")
definition H where "H x \<equiv> exp (c / 2 * (ln x) powr (1 / 2))" for x :: real
definition T where "T x \<equiv> exp (c * (ln x) powr (1 / 2))" for x :: real
definition a where "a x \<equiv> 1 - C\<^sub>4 / (c * (ln x) powr (1 / 2))" for x :: real
definition b where "b x \<equiv> 1 + 1 / (ln x)" for x :: real
definition B where "B x \<equiv> 5 / 4 * ln x" for x :: real
definition f where "f x s \<equiv> x powr s / s * logderiv zeta s" for x :: real and s :: complex
definition R where "R x \<equiv>
  x powr (b x) * H x * B x / T x + 3 * (2 + ln (T x / b x))
  * (\<Sum>n | x - x / H x \<le> n \<and> n \<le> x + x / H x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>)" for x :: real
definition Rc' where "Rc' \<equiv> O(\<lambda>x. x * exp (- (c / 2 - \<epsilon>) * ln x powr (1 / 2)))"
definition Rc where "Rc \<equiv> O(\<lambda>x. x * exp (- (c / 2 - 2 * \<epsilon>) * ln x powr (1 / 2)))"
definition z\<^sub>1 where "z\<^sub>1 x \<equiv> Complex (a x) (- T x)" for x
definition z\<^sub>2 where "z\<^sub>2 x \<equiv> Complex (b x) (- T x)" for x
definition z\<^sub>3 where "z\<^sub>3 x \<equiv> Complex (b x) (T x)" for x
definition z\<^sub>4 where "z\<^sub>4 x \<equiv> Complex (a x) (T x)" for x
definition rect where "rect x \<equiv> cbox (z\<^sub>1 x) (z\<^sub>3 x)" for x
definition rect' where "rect' x \<equiv> rect x - {1}" for x
definition P\<^sub>t where "P\<^sub>t x t \<equiv> linepath (Complex (a x) t) (Complex (b x) t)" for x t
definition P\<^sub>1 where "P\<^sub>1 x \<equiv> linepath (z\<^sub>1 x) (z\<^sub>4 x)" for x
definition P\<^sub>2 where "P\<^sub>2 x \<equiv> linepath (z\<^sub>2 x) (z\<^sub>3 x)" for x
definition P\<^sub>3 where "P\<^sub>3 x \<equiv> P\<^sub>t x (- T x)" for x
definition P\<^sub>4 where "P\<^sub>4 x \<equiv> P\<^sub>t x (T x)" for x
definition P\<^sub>r where "P\<^sub>r x \<equiv> rectpath (z\<^sub>1 x) (z\<^sub>3 x)" for x

lemma Rc_eq_rem_est:
  "Rc = rem_est (c / 2 - 2 * \<epsilon>) (1 / 2) 0"
proof -
  have *: "\<forall>\<^sub>F x :: real in at_top. 0 < ln (ln x)" by real_asymp
  show ?thesis unfolding Rc_def rem_est_def
    by (rule landau_o.big.cong) (use * in eventually_elim, auto)
qed

lemma residue_f:
  "residue (f x) 1 = - x"
proof -
  define A where "A \<equiv> box (Complex 0 (- 1 / 2)) (Complex 2 (1 / 2))"
  have hA: "0 \<notin> A" "1 \<in> A" "open A"
    unfolding A_def by (auto simp add: mem_box Basis_complex_def)
  have "zeta' s \<noteq> 0" when "s \<in> A" for s
  proof -
    have "s \<noteq> 1 \<Longrightarrow> zeta s \<noteq> 0"
      using that unfolding A_def
      by (intro zeta_nonzero_small_imag)
         (auto simp add: mem_box Basis_complex_def)
    thus ?thesis by (subst zeta'_eq_zero_iff) auto
  qed
  hence h: "(\<lambda>s. x powr s / s * logderiv zeta' s) holomorphic_on A"
    by (intro holomorphic_intros) (use hA in auto)
  have h': "(\<lambda>s. x powr s / (s * (s - 1))) holomorphic_on A - {1}"
    by (auto intro!: holomorphic_intros) (use hA in auto)
  have s_ne_1: "\<forall>\<^sub>F s :: complex in at 1. s \<noteq> 1"
    by (subst eventually_at_filter) auto
  moreover have "\<forall>\<^sub>F s in at 1. zeta s \<noteq> 0"
    by (intro non_zero_neighbour_pole is_pole_zeta)
  ultimately have "\<forall>\<^sub>F s in at 1. logderiv zeta s = logderiv zeta' s - 1 / (s - 1)"
    by eventually_elim (rule logderiv_zeta_eq_zeta')
  moreover have
    "f x s = x powr s / s * logderiv zeta' s - x powr s / s / (s - 1)"
    when "logderiv zeta s = logderiv zeta' s - 1 / (s - 1)" "s \<noteq> 0" "s \<noteq> 1" for s :: complex
    unfolding f_def by (subst that(1)) (insert that, auto simp add: field_simps)
  hence "\<forall>\<^sub>F s :: complex in at 1. s \<noteq> 0 \<longrightarrow> s \<noteq> 1
    \<longrightarrow> logderiv zeta s = logderiv zeta' s - 1 / (s - 1)
    \<longrightarrow> f x s = x powr s / s * logderiv zeta' s - x powr s / s / (s - 1)"
    by (intro eventuallyI) blast
  moreover have "\<forall>\<^sub>F s :: complex in at 1. s \<noteq> 0"
    by (subst eventually_at_topological)
       (intro exI [of _ "UNIV - {0}"], auto)
  ultimately have "\<forall>\<^sub>F s :: complex in at 1. f x s = x powr s / s * logderiv zeta' s - x powr s / s / (s - 1)"
    using s_ne_1 by eventually_elim blast
  hence "residue (f x) 1 = residue (\<lambda>s. x powr s / s * logderiv zeta' s - x powr s / s / (s - 1)) 1"
    by (intro residue_cong refl)
  also have "\<dots> = residue (\<lambda>s. x powr s / s * logderiv zeta' s) 1 - residue (\<lambda>s. x powr s / s / (s - 1)) 1"
    by (subst residue_diff [where ?s = A]) (use h h' hA in auto)
  also have "\<dots> = - x"
  proof -
    have "residue (\<lambda>s. x powr s / s * logderiv zeta' s) 1 = 0"
      by (rule residue_holo [where ?s = A]) (use hA h in auto)
    moreover have "residue (\<lambda>s. x powr s / s / (s - 1)) 1 = (x :: complex) powr 1 / 1"
      by (rule residue_simple [where ?s = A]) (use hA in \<open>auto intro!: holomorphic_intros\<close>)
    ultimately show ?thesis by auto
  qed
  finally show ?thesis .
qed

lemma rect_in_strip:
  "rect x - {1} \<subseteq> zeta_strip_region (a x) (T x)"
  unfolding rect_def zeta_strip_region_def z\<^sub>1_def z\<^sub>3_def
  by (auto simp add: in_cbox_complex_iff)

lemma rect_in_strip':
  "{s \<in> rect x. C\<^sub>3 \<le> \<bar>Im s\<bar>} \<subseteq> zeta_strip_region' (a x) (T x)"
  unfolding rect_def zeta_strip_region'_def z\<^sub>1_def z\<^sub>3_def
  using C\<^sub>3_gt_zero by (auto simp add: in_cbox_complex_iff)

lemma
  rect'_in_zerofree: "\<forall>\<^sub>F x in at_top. rect' x \<subseteq> zeta_zerofree_region" and
  rect_in_logderiv_zeta: "\<forall>\<^sub>F x in at_top. {s \<in> rect x. C\<^sub>3 \<le> \<bar>Im s\<bar>} \<subseteq> logderiv_zeta_region"
proof (goal_cases)
  case 1 have
    "\<forall>\<^sub>F x in at_top. C\<^sub>4 / ln x \<le> C\<^sub>1 / (7 * ln (x + 3))" by (rule C\<^sub>4_prop)
  moreover have "LIM x at_top. exp (c * (ln x) powr (1 / 2)) :> at_top" using Hc by real_asymp
  ultimately have h:
   "\<forall>\<^sub>F x in at_top. C\<^sub>4 / ln (exp (c * (ln x) powr (1 / 2)))
    \<le> C\<^sub>1 / (7 * ln (exp (c * (ln x) powr (1 / 2)) + 3))" (is "eventually ?P _")
    by (rule eventually_compose_filterlim)
  moreover have
    "?P x \<Longrightarrow> zeta_strip_region (a x) (T x) \<subseteq> zeta_zerofree_region"
    (is "_ \<Longrightarrow> ?Q") for x unfolding T_def a_def
    by (intro strip_in_zerofree_region strip_condition_imp) auto
  hence "\<forall>\<^sub>F x in at_top. ?P x \<longrightarrow> ?Q x" by (intro eventuallyI) blast
  ultimately show ?case unfolding rect'_def by eventually_elim (use rect_in_strip in auto)
  case 2 from h have
    "?P x \<Longrightarrow> zeta_strip_region' (a x) (T x) \<subseteq> logderiv_zeta_region"
    (is "_ \<Longrightarrow> ?Q") for x unfolding T_def a_def
    by (intro strip_in_logderiv_zeta_region) auto
  hence "\<forall>\<^sub>F x in at_top. ?P x \<longrightarrow> ?Q x" by (intro eventuallyI) blast
  thus ?case using h by eventually_elim (use rect_in_strip' in auto)
qed

lemma zeta_nonzero_in_rect:
  "\<forall>\<^sub>F x in at_top. \<forall>s. s \<in> rect' x \<longrightarrow> zeta s \<noteq> 0"
  using rect'_in_zerofree by eventually_elim (use zeta_zerofree_region in auto)

lemma zero_notin_rect: "\<forall>\<^sub>F x in at_top. 0 \<notin> rect' x"
proof -
  have "\<forall>\<^sub>F x in at_top. C\<^sub>4 / (c * (ln x) powr (1 / 2)) < 1"
    using Hc by real_asymp
  thus ?thesis
    unfolding rect'_def rect_def z\<^sub>1_def z\<^sub>4_def T_def a_def
    by eventually_elim (simp add: in_cbox_complex_iff)
qed

lemma f_analytic:
  "\<forall>\<^sub>F x in at_top. f x analytic_on rect' x"
  using zeta_nonzero_in_rect zero_notin_rect unfolding f_def
  by eventually_elim (intro analytic_intros, auto, simp add: rect'_def)

lemma path_image_in_rect_1:
  assumes "0 \<le> T x \<and> a x \<le> b x"
  shows "path_image (P\<^sub>1 x) \<subseteq> rect x \<and> path_image (P\<^sub>2 x) \<subseteq> rect x"
  unfolding P\<^sub>1_def P\<^sub>2_def rect_def z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def
  by (simp, intro conjI closed_segment_subset)
     (insert assms, auto simp add: in_cbox_complex_iff)

lemma path_image_in_rect_2:
  assumes "0 \<le> T x \<and> a x \<le> b x \<and> t \<in> {-T x..T x}"
  shows "path_image (P\<^sub>t x t) \<subseteq> rect x"
  unfolding P\<^sub>t_def rect_def z\<^sub>1_def z\<^sub>3_def
  by (simp, intro conjI closed_segment_subset)
     (insert assms, auto simp add: in_cbox_complex_iff)

definition path_in_rect' where
"path_in_rect' x \<equiv>
  path_image (P\<^sub>1 x) \<subseteq> rect' x \<and> path_image (P\<^sub>2 x) \<subseteq> rect' x \<and>
  path_image (P\<^sub>3 x) \<subseteq> rect' x \<and> path_image (P\<^sub>4 x) \<subseteq> rect' x"

lemma path_image_in_rect':
  assumes "0 < T x \<and> a x < 1 \<and> 1 < b x"
  shows "path_in_rect' x"
proof -
  have "path_image (P\<^sub>1 x) \<subseteq> rect x \<and> path_image (P\<^sub>2 x) \<subseteq> rect x"
    by (rule path_image_in_rect_1) (use assms in auto)
  moreover have "path_image (P\<^sub>3 x) \<subseteq> rect x" "path_image (P\<^sub>4 x) \<subseteq> rect x"
    unfolding P\<^sub>3_def P\<^sub>4_def
    by (intro path_image_in_rect_2, (use assms in auto)[1])+
  moreover have
    "1 \<notin> path_image (P\<^sub>1 x) \<and> 1 \<notin> path_image (P\<^sub>2 x) \<and>
     1 \<notin> path_image (P\<^sub>3 x) \<and> 1 \<notin> path_image (P\<^sub>4 x)"
    unfolding P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def P\<^sub>t_def z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def using assms
    by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)
  ultimately show ?thesis unfolding path_in_rect'_def rect'_def by blast
qed

lemma asymp_1:
  "\<forall>\<^sub>F x in at_top. 0 < T x \<and> a x < 1 \<and> 1 < b x"
  unfolding T_def a_def b_def
  by (intro eventually_conj, insert Hc C\<^sub>4_gt_zero) (real_asymp)+

lemma f_continuous_on:
  "\<forall>\<^sub>F x in at_top. \<forall>A\<subseteq>rect' x. continuous_on A (f x)"
  using f_analytic
  by (eventually_elim, safe)
     (intro holomorphic_on_imp_continuous_on analytic_imp_holomorphic,
      elim analytic_on_subset)

lemma contour_integrability:
  "\<forall>\<^sub>F x in at_top.
    f x contour_integrable_on P\<^sub>1 x \<and> f x contour_integrable_on P\<^sub>2 x \<and>
    f x contour_integrable_on P\<^sub>3 x \<and> f x contour_integrable_on P\<^sub>4 x"
proof -
  have "\<forall>\<^sub>F x in at_top. path_in_rect' x"
    using asymp_1 by eventually_elim (rule path_image_in_rect')
  thus ?thesis using f_continuous_on
    unfolding P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def P\<^sub>t_def path_in_rect'_def
    by eventually_elim
       (intro conjI contour_integrable_continuous_linepath,
        fold z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def, auto)
qed

lemma contour_integral_rectpath':
  assumes "f x analytic_on (rect' x)" "0 < T x \<and> a x < 1 \<and> 1 < b x"
  shows "contour_integral (P\<^sub>r x) (f x) = - 2 * pi * \<i> * x"
proof -
  define z where "z \<equiv> (1 + b x) / 2"
  have Hz: "z \<in> box (z\<^sub>1 x) (z\<^sub>3 x)"
    unfolding z\<^sub>1_def z\<^sub>3_def z_def using assms(2)
    by (auto simp add: mem_box Basis_complex_def)
  have Hz': "z \<noteq> 1" unfolding z_def using assms(2) by auto
  have "connected (rect' x)"
  proof -
    have box_nonempty: "box (z\<^sub>1 x) (z\<^sub>3 x) \<noteq> {}" using Hz by auto
    hence "aff_dim (closure (box (z\<^sub>1 x) (z\<^sub>3 x))) = 2"
      by (subst closure_aff_dim, subst aff_dim_open) auto
    thus ?thesis
      unfolding rect'_def using box_nonempty
      by (subst (asm) closure_box)
         (auto intro: connected_punctured_convex simp add: rect_def)
  qed
  moreover have Hz'': "z \<in> rect' x"
    unfolding rect'_def rect_def using box_subset_cbox Hz Hz' by auto
  ultimately obtain T where hT:
    "f x holomorphic_on T" "open T" "rect' x \<subseteq> T" "connected T"
    using analytic_on_holomorphic_connected assms(1) by (metis dual_order.refl)
  define U where "U \<equiv> T \<union> box (z\<^sub>1 x) (z\<^sub>3 x)"
  have one_in_box: "1 \<in> box (z\<^sub>1 x) (z\<^sub>3 x)"
    unfolding z\<^sub>1_def z\<^sub>3_def z_def using assms(2) by (auto simp add: mem_box Basis_complex_def)
  have "contour_integral (P\<^sub>r x) (f x) = 2 * pi * \<i> *
    (\<Sum>s\<in>{1}. winding_number (P\<^sub>r x) s * residue (f x) s)"
  proof (rule Residue_theorem)
    show "finite {1}" "valid_path (P\<^sub>r x)" "pathfinish (P\<^sub>r x) = pathstart (P\<^sub>r x)"
      unfolding P\<^sub>r_def by auto
    show "open U" unfolding U_def using hT(2) by auto
    show "connected U" unfolding U_def
      by (intro connected_Un hT(4) convex_connected)
         (use Hz Hz'' hT(3) in auto)
    have "f x holomorphic_on box (z\<^sub>1 x) (z\<^sub>3 x) - {1}"
      by (rule holomorphic_on_subset, rule analytic_imp_holomorphic, rule assms(1))
         (unfold rect'_def rect_def, use box_subset_cbox in auto)
    hence "f x holomorphic_on ((T - {1}) \<union> (box (z\<^sub>1 x) (z\<^sub>3 x) - {1}))"
      by (intro holomorphic_on_Un) (use hT(1) hT(2) in auto)
    moreover have "\<dots> = U - {1}" unfolding U_def by auto
    ultimately show "f x holomorphic_on U - {1}" by auto
    have Hz: "Re (z\<^sub>1 x) \<le> Re (z\<^sub>3 x)" "Im (z\<^sub>1 x) \<le> Im (z\<^sub>3 x)"
      unfolding z\<^sub>1_def z\<^sub>3_def using assms(2) by auto
    have "path_image (P\<^sub>r x) = rect x - box (z\<^sub>1 x) (z\<^sub>3 x)"
      unfolding rect_def P\<^sub>r_def
      by (intro path_image_rectpath_cbox_minus_box Hz)
    thus "path_image (P\<^sub>r x) \<subseteq> U - {1}"
      using one_in_box hT(3) U_def unfolding rect'_def by auto
    have hU': "rect x \<subseteq> U"
      using hT(3) one_in_box unfolding U_def rect'_def by auto
    show "\<forall>z. z \<notin> U \<longrightarrow> winding_number (P\<^sub>r x) z = 0"
    proof (safe, goal_cases)
      case (1 z) thus ?case unfolding P\<^sub>r_def using hU'
        by (subst winding_number_rectpath_outside)
           (fold rect_def, auto intro: Hz)
    qed
  qed
  also have "\<dots> = - 2 * pi * \<i> * x" unfolding P\<^sub>r_def
    by (simp add: residue_f, subst winding_number_rectpath, auto intro: one_in_box)
  finally show ?thesis .
qed

lemma contour_integral_rectpath:
  "\<forall>\<^sub>F x in at_top. contour_integral (P\<^sub>r x) (f x) = - 2 * pi * \<i> * x"
  using f_analytic asymp_1 by eventually_elim (rule contour_integral_rectpath')

lemma valid_paths:
  "valid_path (P\<^sub>1 x)" "valid_path (P\<^sub>2 x)" "valid_path (P\<^sub>3 x)" "valid_path (P\<^sub>4 x)"
  unfolding P\<^sub>1_def P\<^sub>2_def P\<^sub>3_def P\<^sub>4_def P\<^sub>t_def by auto

lemma integral_rectpath_split:
  assumes "f x contour_integrable_on P\<^sub>1 x \<and> f x contour_integrable_on P\<^sub>2 x \<and>
           f x contour_integrable_on P\<^sub>3 x \<and> f x contour_integrable_on P\<^sub>4 x"
  shows "contour_integral (P\<^sub>3 x) (f x) + contour_integral (P\<^sub>2 x) (f x)
       - contour_integral (P\<^sub>4 x) (f x) - contour_integral (P\<^sub>1 x) (f x) = contour_integral (P\<^sub>r x) (f x)"
proof -
  define Q\<^sub>1 where "Q\<^sub>1 \<equiv> linepath (z\<^sub>3 x) (z\<^sub>4 x)"
  define Q\<^sub>2 where "Q\<^sub>2 \<equiv> linepath (z\<^sub>4 x) (z\<^sub>1 x)"
  have Q_eq: "Q\<^sub>1 = reversepath (P\<^sub>4 x)" "Q\<^sub>2 = reversepath (P\<^sub>1 x)"
    unfolding Q\<^sub>1_def Q\<^sub>2_def P\<^sub>1_def P\<^sub>4_def P\<^sub>t_def by (fold z\<^sub>3_def z\<^sub>4_def) auto
  hence "contour_integral Q\<^sub>1 (f x) = - contour_integral (P\<^sub>4 x) (f x)"
        "contour_integral Q\<^sub>2 (f x) = - contour_integral (P\<^sub>1 x) (f x)"
    by (auto intro: contour_integral_reversepath valid_paths)
  moreover have "contour_integral (P\<^sub>3 x +++ P\<^sub>2 x +++ Q\<^sub>1 +++ Q\<^sub>2) (f x)
       = contour_integral (P\<^sub>3 x) (f x) + contour_integral (P\<^sub>2 x) (f x)
       + contour_integral Q\<^sub>1 (f x) + contour_integral Q\<^sub>2 (f x)"
  proof -
    have 1: "pathfinish (P\<^sub>2 x) = pathstart (Q\<^sub>1 +++ Q\<^sub>2)" "pathfinish Q\<^sub>1 = pathstart Q\<^sub>2"
      unfolding P\<^sub>2_def Q\<^sub>1_def Q\<^sub>2_def by auto
    have 2: "valid_path Q\<^sub>1" "valid_path Q\<^sub>2" unfolding Q\<^sub>1_def Q\<^sub>2_def by auto
    have 3: "f x contour_integrable_on P\<^sub>1 x" "f x contour_integrable_on P\<^sub>2 x"
            "f x contour_integrable_on P\<^sub>3 x" "f x contour_integrable_on P\<^sub>4 x"
            "f x contour_integrable_on Q\<^sub>1" "f x contour_integrable_on Q\<^sub>2"
      using assms by (auto simp add: Q_eq intro: contour_integrable_reversepath valid_paths)
    show ?thesis by (subst contour_integral_join |
      auto intro: valid_paths valid_path_join contour_integrable_joinI 1 2 3)+
  qed
  ultimately show ?thesis
    unfolding P\<^sub>r_def z\<^sub>1_def z\<^sub>3_def rectpath_def
    by (simp add: Let_def, fold P\<^sub>t_def P\<^sub>3_def z\<^sub>1_def z\<^sub>2_def z\<^sub>3_def z\<^sub>4_def)
       (fold P\<^sub>2_def Q\<^sub>1_def Q\<^sub>2_def, auto)
qed

lemma P\<^sub>2_eq:
  "\<forall>\<^sub>F x in at_top. contour_integral (P\<^sub>2 x) (f x) + 2 * pi * \<i> * x
  = contour_integral (P\<^sub>1 x) (f x) - contour_integral (P\<^sub>3 x) (f x) + contour_integral (P\<^sub>4 x) (f x)"
proof -
  have "\<forall>\<^sub>F x in at_top. contour_integral (P\<^sub>3 x) (f x) + contour_integral (P\<^sub>2 x) (f x)
      - contour_integral (P\<^sub>4 x) (f x) - contour_integral (P\<^sub>1 x) (f x) = - 2 * pi * \<i> * x"
    using contour_integrability contour_integral_rectpath asymp_1 f_analytic
    by eventually_elim (metis integral_rectpath_split)
  thus ?thesis by (auto simp add: field_simps)
qed

lemma ev_le_imp_exp_bigo:
  fixes f g :: "real \<Rightarrow> real"
  assumes hf: "\<forall>\<^sub>F x in at_top. 0 < f x"
    and hg: "\<forall>\<^sub>F x in at_top. 0 < g x"
    and le: "\<forall>\<^sub>F x in at_top. ln (f x) \<le> ln (g x)"
  shows "f \<in> O(g)"
proof -
  have "\<forall>\<^sub>F x in at_top. exp (ln (f x)) \<le> exp (ln (g x))"
    using le by simp
  hence "\<forall>\<^sub>F x in at_top. \<parallel>f x\<parallel> \<le> 1 * \<parallel>g x\<parallel>"
    using hf hg by eventually_elim auto
  thus ?thesis by (intro bigoI)
qed

lemma estimation_P\<^sub>1:
  "(\<lambda>x. \<parallel>contour_integral (P\<^sub>1 x) (f x)\<parallel>) \<in> Rc"
proof -
  define r where "r x \<equiv>
    C\<^sub>5 * (c * (ln x) powr (1 / 2))\<^sup>2 * x powr a x * ln (1 + T x / a x)" for x
  note logderiv_zeta_bound_vertical
  moreover have "LIM x at_top. T x :> at_top"
    unfolding T_def using Hc by real_asymp
  ultimately have "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> T x
    \<longrightarrow> \<parallel>logderiv zeta (Complex (1 - C\<^sub>4 / ln (T x)) t)\<parallel> \<le> C\<^sub>5 * (ln (T x))\<^sup>2"
    unfolding a_def by (rule eventually_compose_filterlim)
  hence "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> \<le> T x
    \<longrightarrow> \<parallel>logderiv zeta (Complex (a x) t)\<parallel> \<le> C\<^sub>5 * (c * (ln x) powr (1 / 2))\<^sup>2"
    unfolding a_def T_def by auto
  moreover have "\<forall>\<^sub>F x in at_top. (f x) contour_integrable_on (P\<^sub>1 x)"
    using contour_integrability by eventually_elim auto
  hence "\<forall>\<^sub>F x in at_top. (\<lambda>s. logderiv zeta s * x powr s / s) contour_integrable_on (P\<^sub>1 x)"
     unfolding f_def by eventually_elim (auto simp add: field_simps)
  moreover have "\<forall>\<^sub>F x :: real in at_top. 0 < x" by auto
  moreover have "\<forall>\<^sub>F x in at_top. 0 < a x" unfolding a_def using Hc by real_asymp
  ultimately have "\<forall>\<^sub>F x in at_top.
    \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>1 x) (\<lambda>s. logderiv zeta s * x powr s / s)\<parallel> \<le> r x"
    unfolding r_def P\<^sub>1_def z\<^sub>1_def z\<^sub>4_def using asymp_1
    by eventually_elim (rule perron_aux_3', auto)
  hence "\<forall>\<^sub>F x in at_top. \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>1 x) (f x)\<parallel> \<le> r x"
    unfolding f_def by eventually_elim (auto simp add: mult_ac)
  hence "(\<lambda>x. \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>1 x) (f x)\<parallel>) \<in> O(r)"
    unfolding f_def by (rule eventually_le_imp_bigo')
  moreover have "r \<in> Rc"
  proof -
    define r\<^sub>1 where "r\<^sub>1 x \<equiv> C\<^sub>5 * c\<^sup>2 * ln x * ln (1 + T x / a x)" for x
    define r\<^sub>2 where "r\<^sub>2 x \<equiv> exp (a x * ln x)" for x
    have "r\<^sub>1 \<in> O(\<lambda>x. (ln x)\<^sup>2)"
      unfolding r\<^sub>1_def T_def a_def using Hc C\<^sub>5_gt_zero by real_asymp
    moreover have "r\<^sub>2 \<in> Rc'"
    proof -
      have 1: "\<parallel>r\<^sub>2 x\<parallel> \<le> x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2))"
        when h: "0 < x" "0 < ln x" for x
      proof -
        have "a x * ln x = ln x + - C\<^sub>4 / c * (ln x) powr (1 / 2)"
          unfolding a_def using h(2) Hc
          by (auto simp add: field_simps powr_add [symmetric] frac_eq_eq)
        hence "r\<^sub>2 x = exp (\<dots>)" unfolding r\<^sub>2_def by blast
        also have "\<dots> = x * exp (- C\<^sub>4 / c * (ln x) powr (1 / 2))"
          by (subst exp_add) (use h(1) in auto)
        also have "\<dots> \<le> x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2))"
          by (intro mult_left_mono, subst exp_le_cancel_iff, intro mult_right_mono)
             (use Hc Hc' H\<epsilon> C\<^sub>4_gt_zero h in \<open>auto simp: field_simps intro: add_increasing2\<close>)
        finally show ?thesis unfolding r\<^sub>2_def by auto
      qed
      have "\<forall>\<^sub>F x in at_top. \<parallel>r\<^sub>2 x\<parallel> \<le> x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2))"
        using ln_asymp_pos x_asymp_pos by eventually_elim (rule 1)
      thus ?thesis unfolding Rc'_def by (rule eventually_le_imp_bigo)
    qed
    ultimately have "(\<lambda>x. r\<^sub>1 x * r\<^sub>2 x)
      \<in> O(\<lambda>x. (ln x)\<^sup>2 * (x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2))))"
      unfolding Rc'_def by (rule landau_o.big.mult)
    moreover have "(\<lambda>x. (ln x)\<^sup>2 * (x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2)))) \<in> Rc"
      unfolding Rc_def using Hc H\<epsilon>
      by (real_asymp simp add: field_simps)
    ultimately have "(\<lambda>x. r\<^sub>1 x * r\<^sub>2 x) \<in> Rc"
      unfolding Rc_def by (rule landau_o.big_trans)
    moreover have "\<forall>\<^sub>F x in at_top. r x = r\<^sub>1 x * r\<^sub>2 x"
      using ln_ln_asymp_pos ln_asymp_pos x_asymp_pos
      unfolding r_def r\<^sub>1_def r\<^sub>2_def a_def powr_def power2_eq_square
      by (eventually_elim) (simp add: field_simps exp_add [symmetric])
    ultimately show ?thesis unfolding Rc_def
      by (rule_tac landau_o.big.ev_eq_trans2)
  qed
  ultimately have "(\<lambda>x. \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>1 x) (f x)\<parallel>) \<in> Rc"
    unfolding Rc_def by (rule landau_o.big_trans)
  thus ?thesis unfolding Rc_def by (simp add: norm_divide)
qed

lemma estimation_P\<^sub>t':
  assumes h:
    "1 < x \<and> max 1 C\<^sub>3 \<le> T x" "a x < 1 \<and> 1 < b x"
    "{s \<in> rect x. C\<^sub>3 \<le> \<bar>Im s\<bar>} \<subseteq> logderiv_zeta_region"
    "f x contour_integrable_on P\<^sub>3 x \<and> f x contour_integrable_on P\<^sub>4 x"
    and Ht: "\<bar>t\<bar> = T x"
  shows "\<parallel>contour_integral (P\<^sub>t x t) (f x)\<parallel> \<le> C\<^sub>2 * exp 1 * x / T x * (ln (T x + 3))\<^sup>2 * (b x - a x)"
proof -
  consider "t = T x" | "t = - T x" using Ht by fastforce
  hence "f x contour_integrable_on P\<^sub>t x t"
    using Ht h(4) unfolding P\<^sub>t_def P\<^sub>3_def P\<^sub>4_def by cases auto
  moreover have "\<parallel>f x s\<parallel> \<le> exp 1 * x / T x * (C\<^sub>2 * (ln (T x + 3))\<^sup>2)"
    when "s \<in> closed_segment (Complex (a x) t) (Complex (b x) t)" for s
  proof -
    have Hs: "s \<in> path_image (P\<^sub>t x t)" using that unfolding P\<^sub>t_def by auto
    have "path_image (P\<^sub>t x t) \<subseteq> rect x"
      by (rule path_image_in_rect_2) (use h(2) Ht in auto)
    moreover have Hs': "Re s \<le> b x" "Im s = t"
    proof -
      have "u \<le> 1 \<Longrightarrow> (1 - u) * a x \<le> (1 - u) * b x" for u
        using h(2) by (intro mult_left_mono) auto
      thus "Re s \<le> b x" "Im s = t"
        using that h(2) unfolding closed_segment_def
        by (auto simp add: legacy_Complex_simps field_simps)
    qed
    hence "C\<^sub>3 \<le> \<bar>Im s\<bar>" using h(1) Ht by auto
    ultimately have "s \<in> logderiv_zeta_region" using Hs h(3) by auto
    hence "\<parallel>logderiv zeta s\<parallel> \<le> C\<^sub>2 * (ln (\<bar>Im s\<bar> + 3))\<^sup>2"
      by (rule logderiv_zeta_region_estimate)
    also have "\<dots> = C\<^sub>2 * (ln (T x + 3))\<^sup>2" using Hs'(2) Ht by auto
    also have "\<parallel>x powr s / s\<parallel> \<le> exp 1 * x / T x"
    proof -
      have "\<parallel>x powr s\<parallel> = Re x powr Re s" using h(1) by (intro norm_powr_real_powr) auto
      also have "\<dots> = x powr Re s" by auto
      also have "\<dots> \<le> x powr b x" by (intro powr_mono Hs') (use h(1) in auto)
      also have "\<dots> = exp 1 * x"
        using h(1) unfolding powr_def b_def by (auto simp add: field_simps exp_add)
      finally have "\<parallel>x powr s\<parallel> \<le> exp 1 * x" .
      moreover have "T x \<le> \<parallel>s\<parallel>" using abs_Im_le_cmod [of s] Hs'(2) h(1) Ht by auto
      hence 1: "\<parallel>x powr s\<parallel> / \<parallel>s\<parallel> \<le> \<parallel>x powr s\<parallel> / T x"
        using h(1) by (intro divide_left_mono mult_pos_pos) auto
      ultimately have "\<dots> \<le> exp 1 * x / T x"
        by (intro divide_right_mono) (use h(1) in auto)
      thus ?thesis using 1 by (subst norm_divide) linarith
    qed
    ultimately show ?thesis unfolding f_def
      by (subst norm_mult, intro mult_mono, auto)
         (metis norm_ge_zero order.trans)
  qed
  ultimately have "\<parallel>contour_integral (P\<^sub>t x t) (f x)\<parallel>
    \<le> exp 1 * x / T x * (C\<^sub>2 * (ln (T x + 3))\<^sup>2) * \<parallel>Complex (b x) t - Complex (a x) t\<parallel>"
    unfolding P\<^sub>t_def
    by (intro contour_integral_bound_linepath)
       (use C\<^sub>2_gt_zero h(1) in auto)
  also have "\<dots> = C\<^sub>2 * exp 1 * x / T x * (ln (T x + 3))\<^sup>2 * (b x - a x)"
    using h(2) by (simp add: legacy_Complex_simps)
  finally show ?thesis .
qed

lemma estimation_P\<^sub>t:
  "(\<lambda>x. \<parallel>contour_integral (P\<^sub>3 x) (f x)\<parallel>) \<in> Rc \<and>
   (\<lambda>x. \<parallel>contour_integral (P\<^sub>4 x) (f x)\<parallel>) \<in> Rc"
proof -
  define r where "r x \<equiv> C\<^sub>2 * exp 1 * x / T x * (ln (T x + 3))\<^sup>2 * (b x - a x)" for x
  define p where "p x \<equiv> \<parallel>contour_integral (P\<^sub>3 x) (f x)\<parallel> \<le> r x \<and> \<parallel>contour_integral (P\<^sub>4 x) (f x)\<parallel> \<le> r x" for x
  have "\<forall>\<^sub>F x in at_top. 1 < x \<and> max 1 C\<^sub>3 \<le> T x"
    unfolding T_def by (rule eventually_conj) (simp, use Hc in real_asymp)
  hence "\<forall>\<^sub>F x in at_top. \<forall>t. \<bar>t\<bar> = T x \<longrightarrow> \<parallel>contour_integral (P\<^sub>t x t) (f x)\<parallel> \<le> r x" (is "eventually ?P _")
    unfolding r_def using asymp_1 rect_in_logderiv_zeta contour_integrability
    by eventually_elim (use estimation_P\<^sub>t' in blast)
  moreover have "\<And>x. ?P x \<Longrightarrow> 0 < T x \<Longrightarrow> p x"
    unfolding p_def P\<^sub>3_def P\<^sub>4_def by auto
  hence "\<forall>\<^sub>F x in at_top. ?P x \<longrightarrow> 0 < T x \<longrightarrow> p x"
    by (intro eventuallyI) blast
  ultimately have "\<forall>\<^sub>F x in at_top. p x" using asymp_1 by eventually_elim blast
  hence "\<forall>\<^sub>F x in at_top.
    \<parallel>\<parallel>contour_integral (P\<^sub>3 x) (f x)\<parallel>\<parallel> \<le> 1 * \<parallel>r x\<parallel> \<and>
    \<parallel>\<parallel>contour_integral (P\<^sub>4 x) (f x)\<parallel>\<parallel> \<le> 1 * \<parallel>r x\<parallel>"
    unfolding p_def by eventually_elim auto
  hence "(\<lambda>x. \<parallel>contour_integral (P\<^sub>3 x) (f x)\<parallel>) \<in> O(r) \<and> (\<lambda>x. \<parallel>contour_integral (P\<^sub>4 x) (f x)\<parallel>) \<in> O(r)"
    by (subst (asm) eventually_conj_iff, blast)+
  moreover have "r \<in> Rc"
    unfolding r_def Rc_def a_def b_def T_def using Hc H\<epsilon>
    by (real_asymp simp add: field_simps)
  ultimately show ?thesis
    unfolding Rc_def using landau_o.big_trans by blast
qed

lemma Re_path_P\<^sub>2:
  "\<And>z. z \<in> path_image (P\<^sub>2 x) \<Longrightarrow> Re z = b x"
  unfolding P\<^sub>2_def z\<^sub>2_def z\<^sub>3_def
  by (auto simp add: closed_segment_def legacy_Complex_simps field_simps)

lemma estimation_P\<^sub>2:
  "(\<lambda>x. \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x) + x\<parallel>) \<in> Rc"
proof -
  define r where "r x \<equiv> \<parallel>contour_integral (P\<^sub>1 x) (f x)\<parallel> +
    \<parallel>contour_integral (P\<^sub>3 x) (f x)\<parallel> + \<parallel>contour_integral (P\<^sub>4 x) (f x)\<parallel>" for x
  have [simp]: "\<parallel>a - b + c\<parallel> \<le> \<parallel>a\<parallel> + \<parallel>b\<parallel> + \<parallel>c\<parallel>" for a b c :: complex
    using adhoc_norm_triangle norm_triangle_ineq4 by blast
  have "\<forall>\<^sub>F x in at_top. \<parallel>contour_integral (P\<^sub>2 x) (f x) + 2 * pi * \<i> * x\<parallel> \<le> r x"
    unfolding r_def using P\<^sub>2_eq by eventually_elim auto
  hence "(\<lambda>x. \<parallel>contour_integral (P\<^sub>2 x) (f x) + 2 * pi * \<i> * x\<parallel>) \<in> O(r)"
    by (rule eventually_le_imp_bigo')
  moreover have "r \<in> Rc"
    using estimation_P\<^sub>1 estimation_P\<^sub>t
    unfolding r_def Rc_def by (intro sum_in_bigo) auto
  ultimately have "(\<lambda>x. \<parallel>contour_integral (P\<^sub>2 x) (f x) + 2 * pi * \<i> * x\<parallel>) \<in> Rc"
    unfolding Rc_def by (rule landau_o.big_trans)
  hence "(\<lambda>x. \<parallel>1 / (2 * pi * \<i>) * (contour_integral (P\<^sub>2 x) (f x) + 2 * pi * \<i> * x)\<parallel>) \<in> Rc"
    unfolding Rc_def by (auto simp add: norm_mult norm_divide)
  thus ?thesis by (auto simp add: algebra_simps)
qed

lemma estimation_R:
  "R \<in> Rc"
proof -
  define \<Gamma> where "\<Gamma> x \<equiv> {n :: nat. x - x / H x \<le> n \<and> n \<le> x + x / H x}" for x
  have 1: "(\<lambda>x. x powr b x * H x * B x / T x) \<in> Rc"
    unfolding b_def H_def B_def T_def Rc_def using Hc H\<epsilon>
    by (real_asymp simp add: field_simps)
  have "\<parallel>\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>\<parallel> \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    when h: "0 < x - x / H x" "0 < x / H x" "0 \<le> ln (x + x / H x)" for x
  proof -
    have "\<parallel>\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>\<parallel> = (\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>)"
      by simp (subst abs_of_nonneg, auto intro: sum_nonneg)
    also have "\<dots> = sum mangoldt_real (\<Gamma> x)"
      by (subst norm_fds_mangoldt_complex) (rule refl)
    also have "\<dots> \<le> card (\<Gamma> x) * ln (x + x / H x)"
    proof (rule sum_bounded_above)
      fix n assume "n \<in> \<Gamma> x"
      hence Hn: "0 < n" "n \<le> x + x / H x" unfolding \<Gamma>_def using h by auto
      hence "mangoldt_real n \<le> ln n" by (intro mangoldt_le)
      also have "\<dots> \<le> ln (x + x / H x)" using Hn by auto
      finally show "mangoldt_real n \<le> ln (x + x / H x)" .
    qed
    also have "\<dots> \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    proof -
      have \<Gamma>_eq: "\<Gamma> x = {nat \<lceil>x - x / H x\<rceil>..<nat (\<lfloor>x + x / H x\<rfloor> + 1)}"
        unfolding \<Gamma>_def by (subst nat_le_real_iff) (subst nat_ceiling_le_eq [symmetric], auto)
      moreover have "nat (\<lfloor>x + x / H x\<rfloor> + 1) = \<lfloor>x + x / H x\<rfloor> + 1" using h(1) h(2) by auto
      moreover have "nat \<lceil>x - x / H x\<rceil> = \<lceil>x - x / H x\<rceil>" using h(1) by auto
      moreover have "\<lfloor>x + x / H x\<rfloor> \<le> x + x / H x" by (rule floor_le)
      moreover have "\<lceil>x - x / H x\<rceil> \<ge> x - x / H x" by (rule ceil_ge)
      ultimately have "(nat (\<lfloor>x + x / H x\<rfloor> + 1) :: real) - nat \<lceil>x - x / H x\<rceil> \<le> 2 * x / H x + 1" by linarith
      hence "card (\<Gamma> x) \<le> 2 * x / H x + 1" using h(2) by (subst \<Gamma>_eq) (auto simp add: of_nat_diff_real)
      thus ?thesis using h(3) by (rule mult_right_mono)
    qed
    finally show ?thesis .
  qed
  hence "\<forall>\<^sub>F x in at_top.
    0 < x - x / H x \<longrightarrow> 0 < x / H x \<longrightarrow> 0 \<le> ln (x + x / H x)
    \<longrightarrow> \<parallel>\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>\<parallel> \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    by (intro eventuallyI) blast
  moreover have "\<forall>\<^sub>F x in at_top. 0 < x - x / H x" unfolding H_def using Hc H\<epsilon> by real_asymp
  moreover have "\<forall>\<^sub>F x in at_top. 0 < x / H x" unfolding H_def using Hc H\<epsilon>  by real_asymp
  moreover have "\<forall>\<^sub>F x in at_top. 0 \<le> ln (x + x / H x)" unfolding H_def using Hc H\<epsilon> by real_asymp
  ultimately have "\<forall>\<^sub>F x in at_top. \<parallel>\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>\<parallel> \<le> (2 * x / H x + 1) * ln (x + x / H x)"
    by eventually_elim blast
  hence "(\<lambda>x. \<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>) \<in> O(\<lambda>x. (2 * x / H x + 1) * ln (x + x / H x))"
    by (rule eventually_le_imp_bigo)
  moreover have "(\<lambda>x. (2 * x / H x + 1) * ln (x + x / H x)) \<in> Rc'"
    unfolding Rc'_def H_def using Hc H\<epsilon>
    by (real_asymp simp add: field_simps)
  ultimately have "(\<lambda>x. \<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>) \<in> Rc'"
    unfolding Rc'_def by (rule landau_o.big_trans)
  hence "(\<lambda>x. 3 * (2 + ln (T x / b x)) * (\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>))
      \<in> O(\<lambda>x. 3 * (2 + ln (T x / b x)) * (x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2))))"
    unfolding Rc'_def by (intro landau_o.big.mult_left) auto
  moreover have "(\<lambda>x. 3 * (2 + ln (T x / b x)) * (x * exp (- (c / 2 - \<epsilon>) * (ln x) powr (1 / 2)))) \<in> Rc"
    unfolding Rc_def T_def b_def using Hc H\<epsilon> by (real_asymp simp add: field_simps)
  ultimately have 2: "(\<lambda>x. 3 * (2 + ln (T x / b x)) * (\<Sum>n\<in>\<Gamma> x. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel>)) \<in> Rc"
    unfolding Rc_def by (rule landau_o.big_trans)
  from 1 2 show ?thesis unfolding Rc_def R_def \<Gamma>_def by (rule sum_in_bigo)
qed

lemma perron_psi:
  "\<forall>\<^sub>F x in at_top. \<parallel>\<psi> x + 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel> \<le> R x"
proof -
  have Hb: "\<forall>\<^sub>F x in at_top. 1 < b x" unfolding b_def by real_asymp
  hence "\<forall>\<^sub>F x in at_top. 0 < b x" by eventually_elim auto
  moreover have "\<forall>\<^sub>F x in at_top. b x \<le> T x" unfolding b_def T_def using Hc by real_asymp
  moreover have "\<forall>\<^sub>F x in at_top. abs_conv_abscissa (fds mangoldt_complex) < ereal (b x)"
  proof -
    have "abs_conv_abscissa (fds mangoldt_complex) \<le> 1" by (rule abs_conv_abscissa_mangoldt)
    hence "\<forall>\<^sub>F x in at_top. 1 < b x \<longrightarrow> abs_conv_abscissa (fds mangoldt_complex) < ereal (b x)"
      by (rule_tac eventuallyI)
          (simp add: le_ereal_less one_ereal_def)
    thus ?thesis using Hb by (rule eventually_mp)
  qed
  moreover have "\<forall>\<^sub>F x in at_top. 2 \<le> H x" unfolding H_def using Hc by real_asymp
  moreover have "\<forall>\<^sub>F x in at_top. b x + 1 \<le> H x" unfolding b_def H_def using Hc by real_asymp
  moreover have "\<forall>\<^sub>F x :: real in at_top. 2 \<le> x" by auto
  moreover have "\<forall>\<^sub>F x in at_top.
    (\<Sum>`n\<ge>1. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel> / n nat_powr b x) \<le> B x"
    (is "eventually ?P ?F")
  proof -
    have "?P x" when Hb: "1 < b x \<and> b x \<le> 23 / 20" for x
    proof -
      have "(\<Sum>`n\<ge>1. \<parallel>fds_nth (fds mangoldt_complex) n\<parallel> / n nat_powr (b x))
          = (\<Sum>`n\<ge>1. mangoldt_real n / n nat_powr (b x))"
        by (subst norm_fds_mangoldt_complex) (rule refl)
      also have "\<dots> = - Re (logderiv zeta (b x))"
      proof -
        have "((\<lambda>n. mangoldt_real n * n nat_powr (-b x) * cos (0 * ln (real n)))
            has_sum Re (- deriv zeta (Complex (b x) 0) / zeta (Complex (b x) 0))) {1..}"
          by (intro sums_Re_logderiv_zeta) (use Hb in auto)
        moreover have "Complex (b x) 0 = b x" by (rule complex_eqI) auto
        moreover have "Re (- deriv zeta (b x) / zeta (b x)) = - Re (logderiv zeta (b x))"
          unfolding logderiv_def by auto
        ultimately have "((\<lambda>n. mangoldt_real n * n nat_powr (-b x)) has_sum
                         - Re (logderiv zeta (b x))) {1..}" by auto
        hence "- Re (logderiv zeta (b x)) = (\<Sum>`n\<ge>1. mangoldt_real n * n nat_powr (-b x))"
          by (intro has_sum_imp_has_subsum subsumI)
        also have "\<dots> = (\<Sum>`n\<ge>1. mangoldt_real n / n nat_powr (b x))"
          by (intro subsum_cong) (auto simp add: powr_minus_divide)
        finally show ?thesis by auto
      qed
      also have "\<dots> \<le> \<bar>Re (logderiv zeta (b x))\<bar>" by auto
      also have "\<dots> \<le> \<parallel>logderiv zeta (b x)\<parallel>" by (rule abs_Re_le_cmod)
      also have "\<dots> \<le> 5 / 4 * (1 / (b x - 1))"
        by (rule logderiv_zeta_bound) (use Hb in auto)
      also have "\<dots> = B x" unfolding b_def B_def by auto
      finally show ?thesis .
    qed
    hence "\<forall>\<^sub>F x in at_top. 1 < b x \<and> b x \<le> 23 / 20 \<longrightarrow> ?P x" by auto
    moreover have "\<forall>\<^sub>F x in at_top. b x \<le> 23 / 20" unfolding b_def by real_asymp
    ultimately show ?thesis using Hb by eventually_elim auto
  qed
  ultimately have "\<forall>\<^sub>F x in at_top.
    \<parallel>sum_upto (fds_nth (fds mangoldt_complex)) x - 1 / (2 * pi * \<i>)
      * contour_integral (P\<^sub>2 x) (\<lambda>s. eval_fds (fds mangoldt_complex) s * x powr s / s)\<parallel> \<le> R x"
    unfolding R_def P\<^sub>2_def z\<^sub>2_def z\<^sub>3_def
    by eventually_elim (rule perron_formula(2))
  moreover have "\<forall>\<^sub>F x in at_top. sum_upto (fds_nth (fds mangoldt_complex)) x = \<psi> x" for x :: real
    unfolding primes_psi_def sum_upto_def by auto
  moreover have
     "contour_integral (P\<^sub>2 x) (\<lambda>s. eval_fds (fds mangoldt_complex) s * x powr s / s)
    = contour_integral (P\<^sub>2 x) (\<lambda>s. - (x powr s / s * logderiv zeta s))"
    when "1 < b x" for x
  proof (rule contour_integral_eq, goal_cases)
    case (1 s)
    hence "Re s = b x" by (rule Re_path_P\<^sub>2)
    hence "eval_fds (fds mangoldt_complex) s = - deriv zeta s / zeta s"
      by (intro eval_fds_mangoldt) (use that in auto)
    thus ?case unfolding logderiv_def by (auto simp add: field_simps)
  qed
  hence "\<forall>\<^sub>F x in at_top. 1 < b x \<longrightarrow>
      contour_integral (P\<^sub>2 x) (\<lambda>s. eval_fds (fds mangoldt_complex) s * x powr s / s)
    = contour_integral (P\<^sub>2 x) (\<lambda>s. - (x powr s / s * logderiv zeta s))"
    using Hb by (intro eventuallyI) blast
  ultimately have "\<forall>\<^sub>F x in at_top.
    \<parallel>\<psi> x - 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (\<lambda>s. - (x powr s / s * logderiv zeta s))\<parallel> \<le> R x"
    using Hb by eventually_elim auto
  thus ?thesis unfolding f_def
    by eventually_elim (auto simp add: contour_integral_neg)
qed

lemma estimation_perron_psi:
  "(\<lambda>x. \<parallel>\<psi> x + 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel>) \<in> Rc"
proof -
  have "(\<lambda>x. \<parallel>\<psi> x + 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel>) \<in> O(R)"
    by (intro eventually_le_imp_bigo' perron_psi)
  moreover have "R \<in> Rc" by (rule estimation_R)
  ultimately show ?thesis unfolding Rc_def by (rule landau_o.big_trans)
qed

theorem prime_number_theorem:
  "PNT_3 (c / 2 - 2 * \<epsilon>) (1 / 2) 0"
proof -
  define r where "r x \<equiv>
      \<parallel>\<psi> x + 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel>
    + \<parallel>1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x) + x\<parallel>" for x
  have "\<parallel>\<psi> x - x\<parallel> \<le> r x" for x
  proof -
    have "\<parallel>\<psi> x - x\<parallel> = \<parallel>(\<psi> x :: complex) - x\<parallel>"
      by (fold dist_complex_def, simp add: dist_real_def)
    also have "\<dots> \<le> \<parallel>\<psi> x - - 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel>
      + \<parallel>x - - 1 / (2 * pi * \<i>) * contour_integral (P\<^sub>2 x) (f x)\<parallel>"
      by (fold dist_complex_def, rule dist_triangle2)
    finally show ?thesis unfolding r_def by (simp add: add_ac)
  qed
  hence "(\<lambda>x. \<psi> x - x) \<in> O(r)" by (rule le_imp_bigo)
  moreover have "r \<in> Rc"
    unfolding r_def Rc_def
    by (intro sum_in_bigo, fold Rc_def)
       (rule estimation_perron_psi, rule estimation_P\<^sub>2)
  ultimately show ?thesis unfolding PNT_3_def
    by (subst Rc_eq_rem_est [symmetric], unfold Rc_def)
       (rule landau_o.big_trans)
qed

no_notation primes_psi ("\<psi>")
end

unbundle "prime_counting_notation"

lemma prime_number_theorem:
  shows "(\<lambda>x. \<pi> x - Li x) \<in> O(\<lambda>x. x * exp (- 1 / 4567 * (ln x) powr (1 / 2)))"
proof -
  define c :: real where "c \<equiv> 1 / 2283"
  define \<epsilon> :: real where "\<epsilon> \<equiv> 1 / 41705844"
  interpret z: prime_number_theorem c \<epsilon>
    unfolding c_def \<epsilon>_def by standard (auto simp: C\<^sub>4_def)
  have "PNT_3 (c / 2 - 2 * \<epsilon>) (1 / 2) 0" by (rule z.prime_number_theorem)
  hence "PNT_1 (c / 2 - 2 * \<epsilon>) (1 / 2) 0" by (auto intro: PNT_3_imp_PNT_1)
  thus "(\<lambda>x. \<pi> x - Li x) \<in> O(\<lambda>x. x * exp (- 1 / 4567 * (ln x) powr (1 / 2)))"
    unfolding PNT_1_def rem_est_def c_def \<epsilon>_def
    by (rule landau_o.big.ev_eq_trans1, use ln_ln_asymp_pos in eventually_elim)
       (auto intro: eventually_at_top_linorderI [of 1] simp: powr_half_sqrt)
qed

unbundle "no_prime_counting_notation"
unbundle "no_pnt_notation"
end
