theory pnt
imports
  "Prime_Number_Theorem.Prime_Counting_Functions"
begin
unbundle "prime_counting_notation"
notation powr (infixr "ᣔ" 80)
notation integral ("\<integral>")
notation integrable_on (infixr "\<llangle>\<integral>\<rrangle>" 46)
notation has_integral (infixr "#\<integral>" 46)
notation has_vector_derivative (infix "#vd" 50)
notation has_real_derivative (infix "#rd" 50)
notation absolutely_integrable_on (infixr "║\<integral>║" 46)
notation at_top ("+\<infinity>")
notation at_bot ("-\<infinity>")
notation norm ("║_║")

type_notation nat ("\<nat>")
type_notation int ("\<int>")
type_notation rat ("\<rat>")
type_notation real ("\<real>")
type_notation complex ("\<complex>")

definition rem_est where
"rem_est (c :: \<real>) l
  \<equiv> O(\<lambda> x. x * exp (-c * (ln x) ᣔ (1 / (1 + l))))"

definition Li :: "\<real> \<Rightarrow> \<real>" where
  "Li x \<equiv> \<integral> {2..x} (\<lambda>x. 1 / ln x)"
definition PNT_1 :: "\<real> \<Rightarrow> bool" where
  "PNT_1 l \<equiv> (\<exists>c. (\<lambda> x. \<pi> x - Li x) \<in> rem_est c l)"
definition PNT_2 :: "\<real> \<Rightarrow> bool" where
  "PNT_2 l \<equiv> (\<exists>c. (\<lambda> x. \<theta> x - x) \<in> rem_est c l)"
definition PNT_3 :: "\<real> \<Rightarrow> bool" where
  "PNT_3 l \<equiv> (\<exists>c. (\<lambda> x. \<psi> x - x) \<in> rem_est c l)"

hide_fact Equivalence_Measurable_On_Borel.integral_combine

lemma exp_bigo:
  fixes f g :: "\<real> \<Rightarrow> \<real>"
  assumes "\<forall>\<^sub>F x in +\<infinity>. f x \<le> g x"
  shows "(\<lambda>x. exp (f x)) \<in> O(\<lambda>x. exp (g x))"
proof -
  from assms have "\<forall>\<^sub>F x in +\<infinity>. exp (f x) \<le> exp (g x)" by simp
  hence "\<forall>\<^sub>F x in +\<infinity>. ║exp (f x)║ \<le> 1 * ║exp (g x)║" by simp
  thus ?thesis by blast
qed

lemma rem_est_1:
  fixes c l :: \<real>
  assumes h : "0 < l"
  shows "(\<lambda>x. x ᣔ (2 / 3)) \<in> O(\<lambda>x. x * exp (-c * (ln x) ᣔ (1 / (1 + l))))"
proof -
  from h have "1 / (1 + l) < 1" by (simp add: field_simps)
  hence "(\<forall>\<^sub>F x in +\<infinity>. c * (ln x) ᣔ (1 / (1 + l)) \<le> 1 / 3 * (ln x))" by real_asymp
  hence *: "(\<lambda>x. exp (c * ln x ᣔ (1 / (1 + l)))) \<in> O(\<lambda>x. x ᣔ (1 / 3))"
    by (simp add: exp_bigo powr_def)
  have "(\<lambda>x :: \<real>. x ᣔ (2 / 3)) \<in> O(\<lambda>x. x * x ᣔ (-1 / 3))" by real_asymp
  also have "(\<lambda>x :: \<real>. x * x ᣔ (-1 / 3)) \<in> O(\<lambda>x. x * exp (- c * ln x ᣔ (1 / (1 + l))))"
    using * by (simp add: landau_o.big.inverse exp_minus powr_minus)
  finally show ?thesis.
qed

lemma PNT_3_imp_PNT_2:
  fixes l :: \<real>
  assumes h : "0 < l" and "PNT_3 l"
  shows "PNT_2 l"
proof -
  from \<open>PNT_3 l\<close> obtain c where 1: "(\<lambda> x. \<psi> x - x) \<in> rem_est c l"
    unfolding PNT_3_def by auto
  have "(\<lambda>x. \<psi> x - \<theta> x) \<in> O(\<lambda>x. ln x * sqrt x)" by (rule \<psi>_minus_\<theta>_bigo)
  also have "(\<lambda>x. ln x * sqrt x) \<in> O(\<lambda>x. x ᣔ (2 / 3))" by (real_asymp)
  also have "(\<lambda>x. x ᣔ (2 / 3)) \<in> O(\<lambda>x. x * exp (-c * (ln x) ᣔ (1 / (1 + l))))"
    using h by (rule rem_est_1)
  finally have 2: "(\<lambda>x. \<psi> x - \<theta> x) \<in> rem_est c l" unfolding rem_est_def .
  have 3: "(\<lambda>x. \<theta> x - x) = (\<lambda>x. \<psi> x - x - (\<psi> x - \<theta> x))" by simp
  hence "(\<lambda>x. \<theta> x - x) \<in> rem_est c l"
    using 1 2 unfolding rem_est_def by (subst 3) (rule sum_in_bigo)
  thus ?thesis unfolding PNT_2_def by blast
qed

lemma integrable_cut_1:
  fixes a b c :: \<real> and f :: "\<real> \<Rightarrow> \<real>"
  assumes "a \<le> b" "b \<le> c"
  and Hf: "\<And>x. a \<le> x \<Longrightarrow> f \<llangle>\<integral>\<rrangle> {a..x}"
  shows "f \<llangle>\<integral>\<rrangle> {b..c}"
proof -
  have "a \<le> c" using assms by linarith
  hence "f \<llangle>\<integral>\<rrangle> {a..c}" by (rule Hf)
  thus ?thesis by
    (rule integrable_subinterval_real)
    (subst subset_iff, (subst atLeastAtMost_iff)+,
    blast intro: \<open>a \<le> b\<close> order_trans [of a b])
qed

lemma integral_bigo:
  fixes a :: \<real> and f g :: "\<real> \<Rightarrow> \<real>"
  assumes f_bound: "f \<in> O(g)"
    and Hf:  "\<And>x. a \<le> x \<Longrightarrow> f \<llangle>\<integral>\<rrangle> {a..x}"
    and Hf': "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) \<llangle>\<integral>\<rrangle> {a..x}"
    and Hg': "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. \<bar>g x\<bar>) \<llangle>\<integral>\<rrangle> {a..x}"
  shows "(\<lambda>x. \<integral>{a..x} f) \<in> O(\<lambda>x. 1 + \<integral>{a..x} (\<lambda>x. \<bar>g x\<bar>))"
proof -
  from \<open>f \<in> O(g)\<close> obtain c where "\<forall>\<^sub>F x in +\<infinity>. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>"
    unfolding bigo_def by auto
  then obtain N' :: \<real> where asymp: "\<And>n. n\<ge>N' \<Longrightarrow> \<bar>f n\<bar> \<le> c * \<bar>g n\<bar>"
    by (subst (asm) eventually_at_top_linorder) (blast)
  define N where "N \<equiv> max a N'"
  define I where "I \<equiv> \<bar>\<integral> {a..N} f\<bar>"
  define J where "J \<equiv> \<integral> {a..N} (\<lambda>x. \<bar>g x\<bar>)"
  define c' where "c' \<equiv> max (I + J * \<bar>c\<bar>) \<bar>c\<bar>"
  have "\<And>x. N \<le> x \<Longrightarrow> \<bar>\<integral> {a..x} f\<bar>
      \<le> c' * \<bar>1 + \<integral> {a..x} (\<lambda>x. \<bar>g x\<bar>)\<bar>"
  proof -
    fix x :: \<real>
    assume 1: "N \<le> x"
    define K where "K \<equiv> \<integral> {a..x} (\<lambda>x. \<bar>g x\<bar>)"
    have 2: "a \<le> N" unfolding N_def by linarith
    hence 3: "a \<le> x" using 1 by linarith
    have nnegs: "0 \<le> I" "0 \<le> J" "0 \<le> K"
      unfolding I_def J_def K_def using 1 2 Hg'
      by (auto intro!: integral_nonneg)
    hence abs_eq: "\<bar>I\<bar> = I" "\<bar>J\<bar> = J" "\<bar>K\<bar> = K"
      using nnegs by simp+
    have "\<integral>\<bar>f\<bar>": "(\<lambda>x. \<bar>f x\<bar>) \<llangle>\<integral>\<rrangle> {N..x}"
      using 2 1 Hf' by (rule integrable_cut_1)
    have "\<integral>f": "f \<llangle>\<integral>\<rrangle> {N..x}"
      using 2 1 Hf by (rule integrable_cut_1)
    have "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. c * \<bar>g x\<bar>) \<llangle>\<integral>\<rrangle> {a..x}"
      by (blast intro: Hg' integrable_cmul [OF Hg', simplified])
    hence "\<integral>c\<bar>g\<bar>": "(\<lambda>x. c * \<bar>g x\<bar>) \<llangle>\<integral>\<rrangle> {N..x}"
      using 2 1 by (blast intro: integrable_cut_1)
    have "\<bar>\<integral> {a..x} f\<bar> \<le> I + \<bar>\<integral> {N..x} f\<bar>"
      unfolding I_def
      by (subst integral_combine[OF 2 1 Hf [of x], THEN sym])
         (rule 3, rule abs_triangle_ineq)
    also have "\<dots> \<le> I + \<integral> {N..x} (\<lambda>x. \<bar>f x\<bar>)"
    proof -
      note integral_norm_bound_integral [OF "\<integral>f" "\<integral>\<bar>f\<bar>"]
      then have "\<bar>\<integral> {N..x} f\<bar> \<le> \<integral> {N..x} (\<lambda>x. \<bar>f x\<bar>)" by auto
      then show ?thesis by linarith
    qed also have "\<dots> \<le> I + c * \<integral> {N..x} (\<lambda>x. \<bar>g x\<bar>)"
    proof -
      have 1: "N' \<le> N" unfolding N_def by linarith
      hence "\<And>y :: \<real>. N \<le> y \<Longrightarrow> \<bar>f y\<bar> \<le> c * \<bar>g y\<bar>"
      proof -
        fix y :: \<real>
        assume "N \<le> y"
        thus "\<bar>f y\<bar> \<le> c * \<bar>g y\<bar>"
          by (rule asymp [OF order_trans [OF 1]])
      qed
      hence "\<integral> {N..x} (\<lambda>x. \<bar>f x\<bar>) \<le> \<integral> {N..x} (\<lambda>x. c * \<bar>g x\<bar>)"
        by (rule integral_le [OF "\<integral>\<bar>f\<bar>" "\<integral>c\<bar>g\<bar>"], simp)
      thus ?thesis by simp
    qed also have "\<dots> \<le> I + \<bar>c\<bar> * (J + \<integral> {a..x} (\<lambda>x. ║g x║))"
    proof simp
      note integral_combine[OF 2 1 Hg' [of x]]
      hence K_min_J: "\<integral> {N..x} (\<lambda>x. \<bar>g x\<bar>) = K - J"
        unfolding J_def K_def using 3 by auto
      have "c * (K - J) \<le> \<bar>c\<bar> * (J + K)" proof -
        have "c * (K - J) \<le> \<bar>c * (K - J)\<bar>" by simp
        also have "\<dots> = \<bar>c\<bar> * \<bar>K - J\<bar>" by (simp add: abs_mult)
        also have "\<dots> \<le> \<bar>c\<bar> * (\<bar>J\<bar>+\<bar>K\<bar>)" by (simp add: mult_left_mono)
        finally show ?thesis by (simp add: abs_eq)
      qed
      thus "c * \<integral> {N..x} (\<lambda>x. \<bar>g x\<bar>)
        \<le> \<bar>c\<bar> * (J + \<integral> {a..x} (\<lambda>x. \<bar>g x\<bar>))"
      by (subst K_min_J, fold K_def)
    qed
    also have "\<dots> \<le> c' * \<bar>1 + \<integral> {a..x} (\<lambda>x. \<bar>g x\<bar>)\<bar>"
    by (subst (2) abs_of_nonneg,
       simp add:  integral_nonneg Hg' 3,
       simp add: field_simps,
       subst add.assoc [symmetric],
       rule add_mono, unfold c'_def, auto,
       rule mult_right_mono, auto,
       fold K_def, rule nnegs)
    finally show "\<bar>\<integral> {a..x} f\<bar>
      \<le> c' * \<bar>1 + \<integral> {a..x} (\<lambda>x. \<bar>g x\<bar>)\<bar>".
  qed
  note 0 = this
  show ?thesis proof (rule eventually_mono [THEN bigoI])
    show "\<forall>\<^sub>Fx in +\<infinity>. N \<le> x" by simp
    show "\<And>x. N \<le> x \<Longrightarrow> ║\<integral> {a..x} f║ \<le> c' * 
      ║1 + \<integral> {a..x} (\<lambda>x. \<bar>g x\<bar>)║" by (simp, rule 0)
  qed
qed

section \<open>Implies from PNT_2 to PNT_1\<close>
definition r\<^sub>1 where "r\<^sub>1 x \<equiv> \<pi> x - Li x" for x
definition r\<^sub>2 where "r\<^sub>2 x \<equiv> \<theta> x - x" for x

lemma lm_a1:
  fixes x :: \<real>
  assumes "2 \<le> x"
  shows "\<pi> x = \<theta> x / (ln x) + \<integral> {2..x} (\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2))"
proof -
  note integral_unique [OF \<pi>_conv_\<theta>_integral]
  with assms show ?thesis by auto
qed

theorem integration_by_part':
  fixes a b :: \<real>
    and f g :: "\<real> \<Rightarrow> 'a :: {real_normed_field, banach}"
    and f' g' :: "\<real> \<Rightarrow> 'a"
  assumes "a \<le> b" and
    "continuous_on {a..b} f" and
    "continuous_on {a..b} g" and
    "\<And>x. x \<in> {a..b} \<Longrightarrow> (f has_vector_derivative f' x) (at x)" and
    "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)" and
    int: "(\<lambda>x. f x * g' x) \<llangle>\<integral>\<rrangle> {a..b}"
  shows "((\<lambda>x. f' x * g x) has_integral
    f b * g b - f a * g a - \<integral>{a..b} (\<lambda>x. f x * g' x))
    {a..b}"
proof -
  define prod where "prod \<equiv> (*) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  define y where "y \<equiv> f b * g b - f a * g a - \<integral>{a..b} (\<lambda>x. f x * g' x)"
  have 0: "bounded_bilinear prod" unfolding prod_def
    by (rule bounded_bilinear_mult)
  have 1: "((\<lambda>x. f x * g' x) has_integral f b * g b - f a * g a - y) {a..b}"
  using y_def and int and integrable_integral by auto
  note 2 = integration_by_parts
    [where y = y and prod = prod, OF 0,
     unfolded prod_def]
  from assms and 1 show ?thesis
    by (fold y_def, intro 2) (auto)
qed

lemma lm_a2:
  fixes x :: \<real>
  assumes "2 \<le> x"
  shows
  "(\<lambda>x. 1 / (ln x)\<^sup>2) \<llangle>\<integral>\<rrangle> {2..x}"
  "Li x = x / (ln x) - 2 / (ln 2) + \<integral> {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2)"
proof -
  have 1: "\<And>y :: \<real>. 2 \<le> y \<Longrightarrow>
    DERIV (\<lambda>t. 1 / (ln t)) y :> - (1 / (y * (ln y)\<^sup>2))"
  proof -
    fix y :: \<real> assume Hy: "2 \<le> y"
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
  have 2: "(\<lambda>x. x * (- 1 / (x * (ln x)\<^sup>2))) \<llangle>\<integral>\<rrangle> {2..x}"
    by (rule integrable_continuous_interval)
       ((rule continuous_intros)+, auto)
  have "((\<lambda>x. 1 * (1 / ln x)) #\<integral>
    x * (1 / ln x) - 2 * (1 / ln 2) - \<integral> {2..x} (\<lambda>x. x * (- 1 / (x * (ln x)\<^sup>2)))
    ) {2..x}"
    by (rule integration_by_part', auto, rule \<open>2 \<le> x\<close>,
        auto intro!: continuous_intros,
        subst has_real_derivative_iff_has_vector_derivative [symmetric],
        auto intro: 1, rule 2 [simplified])
  note 3 = this [simplified]
  have "((\<lambda>x. 1 / ln x) #\<integral> (x / ln x - 2 / ln 2 + \<integral> {2..x} (\<lambda>x. 1 / (ln x)\<^sup>2))) {2..x}" proof -
    define a where "a t \<equiv> if t = 0 then 0 else 1 / (ln t)\<^sup>2" for t :: \<real>
    have "\<And>t :: \<real>. t \<in> {2..x} \<Longrightarrow> a t = 1 / (ln t)\<^sup>2"
      unfolding a_def by auto
    hence 4: "\<integral> {2..x} a = \<integral> {2..x} (\<lambda>x. 1 / (ln x)\<^sup>2)" by (rule integral_cong)
    from 3 show ?thesis
      by (subst (asm) 4 [unfolded a_def])
  qed
  thus "Li x = x / ln x - 2 / ln 2 + \<integral> {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2)" unfolding Li_def by auto
  show "(\<lambda>x. 1 / (ln x)\<^sup>2) \<llangle>\<integral>\<rrangle> {2..x}"
    by (rule integrable_continuous_interval)
       ((rule continuous_intros)+, auto)
qed

theorem \<theta>_integrable:
  fixes x :: "\<real>"
  assumes "2 \<le> x"
  shows "(\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2)) \<llangle>\<integral>\<rrangle> {2..x}"
by (rule \<pi>_conv_\<theta>_integral [THEN has_integral_integrable], rule assms)

lemma lm_a3:
  fixes x :: \<real>
  assumes Hx: "2 \<le> x"
  shows "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) \<llangle>\<integral>\<rrangle> {2..x}" (is ?P)
    "r\<^sub>1 x = r\<^sub>2 x / (ln x) + 2 / ln 2 + \<integral> {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))" (is ?Q)
proof -
  have 0: "\<And>t. t \<in> {2..x} \<Longrightarrow> (\<theta> t - t) / (t * (ln t)\<^sup>2) = \<theta> t / (t * (ln t)\<^sup>2) - 1 / (ln t)\<^sup>2"
    by (subst diff_divide_distrib, auto)
  note integrables = \<theta>_integrable lm_a2(1)
  let ?D = "\<integral> {2..x} (\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2)) -
    \<integral> {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2)"
  have "((\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2) - 1 / (ln t)\<^sup>2) #\<integral>
    ?D) {2..x}"
  unfolding r\<^sub>2_def by
    (rule has_integral_diff,
    (rule integrables [THEN integrable_integral], rule Hx)+)
  hence 0: "((\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) #\<integral>
    ?D) {2..x}"
  unfolding r\<^sub>2_def by (subst has_integral_cong [OF 0])
  thus ?P by (rule has_integral_integrable)
  note 1 = 0 [THEN integral_unique]
  have 2: "r\<^sub>2 x / ln x = \<theta> x / ln x - x / ln x"
    unfolding r\<^sub>2_def by (rule diff_divide_distrib)
  from lm_a1 and lm_a2(2) and assms
  have "\<pi> x - Li x = \<theta> x / ln x
    + \<integral> {2..x} (\<lambda>t. \<theta> t / (t * (ln t)\<^sup>2))
    - (x / ln x - 2 / ln 2 + \<integral> {2..x} (\<lambda>t. 1 / (ln t)\<^sup>2))"
    by auto
  also have "\<dots> = r\<^sub>2 x / ln x + 2 / ln 2
    + \<integral> {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))"
    by (subst 2, subst 1) (auto)
  finally show ?Q unfolding r\<^sub>1_def by auto
qed

lemma eventually_at_top_linorderI':
  fixes c :: "'a :: {no_top, linorder}"
  assumes h : "\<And>x. c < x \<Longrightarrow> P x"
  shows "eventually P at_top"
proof (rule eventually_mono)
  show "\<forall>\<^sub>F x in +\<infinity>. c < x" by (rule eventually_gt_at_top)
  from h show "\<And>x. c < x \<Longrightarrow> P x" .
qed

lemma smallo_ln_diverge_1:
  fixes f :: "\<real> \<Rightarrow> \<real>"
  assumes f_ln: "f \<in> o(ln)"
  shows "LIM x +\<infinity>. x * exp (- f x) :> +\<infinity>"
proof -
  have "(1/2 :: \<real>) > 0" by auto
  with f_ln have 0: "\<forall>\<^sub>F x in +\<infinity>. ║f x║ \<le> 1/2 * ║ln x║" unfolding smallo_def by fast
  have "x * exp (-f x) \<ge> x ᣔ (1/2)"
    if 1:"1 \<le> x" and 2:"║f x║ \<le> 1/2 * ║ln x║" for x
  proof -
    have "f x \<le> ║f x║" by auto
    also have "\<dots> \<le> 1/2 * ║ln x║" by (rule 2)
    also have "\<dots> \<le> 1/2 * ln x" using 1 by auto
    finally have 0: "f x \<le> 1/2 * ln x" by auto
    have "x ᣔ (-1/2) = exp (-1/2 * ln x)"
      unfolding powr_def using 1 by auto
    also have "\<dots> \<le> exp (-f x)" using 0 by auto
    finally have 0: "x ᣔ (-1/2) \<le> exp (-f x)" .
    have "x ᣔ (1/2) = x ᣔ (1 + -1/2)" by auto
    also have "\<dots> = x ᣔ 1 * x ᣔ (-1/2)" by (rule powr_add)
    also have "\<dots> = x * x ᣔ (-1/2)" using 1 by auto
    also have "\<dots> \<le> x * exp (-f x)" using 0 1 by auto
    finally show ?thesis .
  qed
  hence "\<forall>\<^sub>F x in +\<infinity>. ║f x║ \<le> 1/2 * ║ln x║ \<longrightarrow> x * exp (-f x) \<ge> x ᣔ (1/2)"
    by (blast intro: eventually_at_top_linorderI)
  hence 0: "\<forall>\<^sub>F x in +\<infinity>. x * exp (-f x) \<ge> x ᣔ (1/2)"
    by (rule eventually_rev_mp [OF 0])
  show "LIM x +\<infinity>. x * exp (- f x) :> +\<infinity>"
    by (rule filterlim_at_top_mono [OF _ 0], real_asymp)
qed

lemma exp_integral_asymp:
  fixes f f' :: "\<real> \<Rightarrow> \<real>"
  assumes cf: "continuous_on {a..} f"
      and der: "\<And>x. a < x \<Longrightarrow> DERIV f x :> f' x"
      and td: "((\<lambda>x. x * f' x) \<longlongrightarrow> 0) +\<infinity>"
      and f_ln: "f \<in> o(ln)"
  shows "(\<lambda>x. \<integral> {a..x} (\<lambda>t. exp (-f t))) \<sim>[+\<infinity>] (\<lambda>x. x * exp(-f x))"
proof (rule asymp_equivI', rule lhospital_at_top_at_top)
  have cont_exp: "continuous_on {a..} (\<lambda>t. exp (- f t))"
    using cf by (simp add: continuous_intros)
  show "\<forall>\<^sub>F x in +\<infinity>. ((\<lambda>x. \<integral> {a..x} (\<lambda>t. exp (- f t)))
    #rd exp (- f x)) (at x)" (is "eventually ?P ?F")
  proof (rule eventually_at_top_linorderI')
    fix x assume 1: "a < x"
    hence 2: "a \<le> x" by linarith
    have 3: "(at x within {a..x+1}) = (at x)"
      by (rule at_within_interior, auto, rule 1)
    show "?P x"
      by (subst 3 [symmetric],
          rule integral_has_real_derivative,
          rule continuous_on_subset [OF cont_exp],
          auto, rule 2)
  qed
  have "\<forall>\<^sub>F x in +\<infinity>. ((\<lambda>x. x * exp (- f x))
    #rd 1 * exp (- f x) + exp (- f x) * (- f' x) * x) (at x)"
    (is "eventually ?P ?F")
  proof (rule eventually_at_top_linorderI')
    fix x assume 1: "a < x"
    hence 2: "(at x within {a<..}) = (at x)"
      by (auto intro: at_within_open)
    show "?P x"
      by (subst 2 [symmetric], (rule derivative_intros)+, subst 2, rule der, rule 1)
  qed
  moreover have
     "1 * exp (- f x) + exp (- f x) * (- f' x) * x
    = exp (- f x) * (1 - x * f' x)" for x :: \<real>
    by (simp add: field_simps)
  ultimately show "\<forall>\<^sub>F x in +\<infinity>. (
        (\<lambda>x. x * exp (- f x))
    #rd exp (- f x) * (1 - x * f' x)) (at x)" by auto
  show "LIM x +\<infinity>. x * exp (- f x) :> +\<infinity>"
    using f_ln by (rule smallo_ln_diverge_1)
  have "((\<lambda>x. 1 / (1 - x * f' x)) \<longlongrightarrow> 1 / (1 - 0)) +\<infinity>" by ((rule tendsto_intros)+, rule td, linarith)
  thus "((\<lambda>x. exp (- f x) / (exp (- f x) * (1 - x * f' x))) \<longlongrightarrow> 1) +\<infinity>" by auto
  have "((\<lambda>x. 1 - x * f' x) \<longlongrightarrow> 1 - 0) +\<infinity>"
    by ((rule tendsto_intros)+, rule td)
  hence 0: "((\<lambda>x. 1 - x * f' x) \<longlongrightarrow> 1) +\<infinity>" by simp
  hence "\<forall>\<^sub>F x in +\<infinity>. 0 < 1 - x * f' x"
    by (rule order_tendstoD) linarith
  moreover have "\<forall>\<^sub>F x in +\<infinity>. 0 < 1 - x * f' x \<longrightarrow> exp (- f x) * (1 - x * f' x) \<noteq> 0" by auto
  ultimately show "\<forall>\<^sub>F x in +\<infinity>. exp (- f x) * (1 - x * f' x) \<noteq> 0" by (rule eventually_rev_mp)
qed

lemma integral_bigo_exp:
  fixes a :: \<real> and f g g' :: "\<real> \<Rightarrow> \<real>"
  assumes f_bound: "f \<in> O(\<lambda>x. exp(-g x))"
    and Hf:  "\<And>x. a \<le> x \<Longrightarrow> f \<llangle>\<integral>\<rrangle> {a..x}"
    and Hf': "\<And>x. a \<le> x \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) \<llangle>\<integral>\<rrangle> {a..x}"
    and Hg:  "continuous_on {a..} g"
    and der: "\<And>x. a < x \<Longrightarrow> DERIV g x :> g' x"
    and td:  "((\<lambda>x. x * g' x) \<longlongrightarrow> 0) +\<infinity>"
    and f_ln:"g \<in> o(ln)"
  shows "(\<lambda>x. \<integral>{a..x} f) \<in> O(\<lambda>x. x * exp(-g x))"
proof -
  have "\<And>y. (\<lambda>x. exp(-g x)) \<llangle>\<integral>\<rrangle> {a..y}"
    by (rule integrable_continuous_interval,
       (rule continuous_intros)+,
        rule continuous_on_subset, rule Hg, auto)
  hence "\<And>y. (\<lambda>x. \<bar>exp(-g x)\<bar>) \<llangle>\<integral>\<rrangle> {a..y}" by simp
  hence "(\<lambda>x. \<integral>{a..x} f) \<in> O(\<lambda>x. 1 + \<integral>{a..x} (\<lambda>x. \<bar>exp(-g x)\<bar>))"
    using assms by (intro integral_bigo)
  hence "(\<lambda>x. \<integral>{a..x} f) \<in> O(\<lambda>x. 1 + \<integral>{a..x} (\<lambda>x. exp(-g x)))" by simp
  also have "(\<lambda>x. 1 + \<integral>{a..x} (\<lambda>x. exp(-g x))) \<in> O(\<lambda>x. x * exp(-g x))"
  proof (rule sum_in_bigo)
    have "LIM x +\<infinity>. x * exp (- g x) :> +\<infinity>"
      using f_ln by (rule smallo_ln_diverge_1)
    hence "\<forall>\<^sub>F x in +\<infinity>. 1 \<le> x * exp (- g x)"
      using filterlim_at_top by fast
    hence "\<forall>\<^sub>F x in +\<infinity>. ║1 :: \<real>║ \<le> 1 * ║x * exp (- g x)║"
      by (rule eventually_rev_mp, auto)
    thus "(\<lambda>x. 1 :: \<real>) \<in> O(\<lambda>x. x * exp (- g x))"
      by (intro bigoI)
    show "(\<lambda>x. \<integral> {a..x} (\<lambda>x. exp (- g x))) \<in> O(\<lambda>x. x * exp (- g x))"
    by (rule asymp_equiv_imp_bigo, rule exp_integral_asymp, auto intro: assms)
  qed
  finally show ?thesis .
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

lemma lm_a4:
  fixes c l :: \<real>
  assumes hl : "0 < l"
  assumes h: "r\<^sub>2 \<in> rem_est c l"
  shows "(\<lambda>x. \<integral> {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))) \<in> rem_est c l"
unfolding rem_est_def
proof (subst minus_mult_left [symmetric],
       rule integral_bigo_exp)
  have hl_1: "1 / (1 + l) < 1"
    using hl by (simp add: field_simps)
  thus "(\<lambda>x. c * ln x ᣔ (1 / (1 + l))) \<in> o(ln)"
    by real_asymp
  show "continuous_on {2..} (\<lambda>x. c * ln x ᣔ (1 / (1 + l)))" by (simp add: continuous_intros)
  show "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) \<llangle>\<integral>\<rrangle> {2..x}"
    if *:"2 \<le> x" for x using * by (rule lm_a3(1))
  let ?g = "\<lambda>x :: \<real>. c * ((1 / (1 + l)) * ln x ᣔ (1 / (1 + l) - 1) * (1 / x))"
  show "((\<lambda>x. c * (ln x ᣔ (1 / (1 + l)))) #rd ?g x) (at x)" if *:"2 < x" for x
  proof -
    have 0: "at x within {2<..} = at x"
      by (rule at_within_open, auto, rule *)
    have "((\<lambda>x. c * (ln x ᣔ (1 / (1 + l)))) #rd ?g x) (at x within {2<..})"
      by (rule derivative_intros DERIV_cmult)+
         (rule rev_mp [OF *], auto, subst 0, rule DERIV_ln_divide, rule rev_mp [OF *], linarith)
    thus ?thesis using 0 by auto
  qed
  show "((\<lambda>x. x * ?g x) \<longlongrightarrow> 0) +\<infinity>"
    using hl_1 by real_asymp
  have nz_1: "\<forall>\<^sub>F t :: \<real> in +\<infinity>. t * (ln t)\<^sup>2 \<noteq> 0"
  proof (rule eventually_at_top_linorderI')
    fix x :: \<real> assume "1 < x"
    thus "x * (ln x)\<^sup>2 \<noteq> 0" by auto
  qed
  have "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))
    \<in> O(\<lambda>x. (x * exp (-c * (ln x) ᣔ (1 / (1 + l)))) / (x * (ln x)\<^sup>2))"
    by (rule landau_o.big.divide_right, rule nz_1, fold rem_est_def, rule h)
  also have "(\<lambda>x. (x * exp (-c * (ln x) ᣔ (1 / (1 + l)))) / (x * (ln x)\<^sup>2))
    \<in> O(\<lambda>x. (x * exp (-c * ln x ᣔ (1 / (1 + l)))) / x)"
    by (rule landau_o.big.divide_left, rule nz_1, auto, real_asymp)
  also have "\<forall>\<^sub>F x in +\<infinity>.
      x * exp (-c * ln x ᣔ (1 / (1 + l))) / x
    = exp (- (c * ln x ᣔ (1 / (1 + l))))"
    by auto
  finally show "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2)) \<in> O(\<lambda>x. exp (- (c * ln x ᣔ (1 / (1 + l)))))" .
  have "(\<lambda>x. r\<^sub>2 x / (x * (ln x)\<^sup>2)) ║\<integral>║ {2..x}"
    if *:"2 \<le> x" for x
  proof (rule set_integrableI_bounded, auto)
    show "emeasure lborel {2..x} < top_class.top"
      using * by auto
    have "(\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2) * indicator {2..x} t) \<in> borel_measurable lebesgue"
      using * by (intro integrable_integral
        [THEN has_integral_implies_lebesgue_measurable_real])
        (rule lm_a3(1))
    thus "(\<lambda>xa. indicator {2..x} xa * r\<^sub>2 xa / (xa * (ln xa)\<^sup>2)) \<in> borel_measurable lebesgue"
    by (simp add: mult_ac)
    let ?C = "(ln 4 + 1) / (ln 2)\<^sup>2 :: \<real>"
    show "AE xa in lebesgue. 2 \<le> xa \<and> xa \<le> x \<longrightarrow> \<bar>r\<^sub>2 xa\<bar> / (xa * (ln xa)\<^sup>2) \<le> ?C"
    proof (rule AE_I2, auto)
      fix t assume "2 \<le> t" "t \<le> x"
      hence h: "1 \<le> t" "2 \<le> t" by linarith+
      hence "0 \<le> \<theta> t \<and> \<theta> t < ln 4 * t"
        by (auto intro: \<theta>_upper_bound)
      hence *:"\<bar>\<theta> t\<bar> \<le> ln 4 * t" by auto
      have "1 \<le> ln t / ln 2" using h by auto
      hence "1 \<le> (ln t / ln 2)\<^sup>2" by auto
      also have "\<dots> = (ln t)\<^sup>2 / (ln 2)\<^sup>2"
        unfolding power2_eq_square by auto
      finally have "1 \<le> (ln t)\<^sup>2 / (ln 2)\<^sup>2" .
      hence "\<bar>r\<^sub>2 t\<bar> \<le> \<bar>\<theta> t\<bar> + \<bar>t\<bar>"
        unfolding r\<^sub>2_def by auto
      also have "\<dots> \<le> ln 4 * t + 1 * t"
        using h * by auto
      also have "\<dots> = (ln 4 + 1) * t"
        by (simp add: algebra_simps)
      also have "\<dots> \<le> (ln 4 + 1) * t * ((ln t)\<^sup>2 / (ln 2)\<^sup>2)"
        by (auto simp add: field_simps)
           (rule add_mono; rule rev_mp[OF h(2)], auto)
      finally have *:"\<bar>r\<^sub>2 t\<bar> \<le> ?C * (t * (ln t)\<^sup>2)"
        by auto
      thus "\<bar>r\<^sub>2 t\<bar> / (t * (ln t)\<^sup>2) \<le> ?C"
        using h * by (auto simp add: field_simps)
    qed
  qed
  thus "\<And>x. 2 \<le> x \<Longrightarrow> (\<lambda>x. \<bar>r\<^sub>2 x / (x * (ln x)\<^sup>2)\<bar>) \<llangle>\<integral>\<rrangle> {2..x}"
  by (fold real_norm_def, rule absolutely_integrable_on_def [THEN iffD1, THEN conjunct2])
qed

lemma lm_a5:
  fixes c l :: \<real>
  assumes hl : "0 < l"
  assumes h: "r\<^sub>2 \<in> rem_est c l"
  shows "(\<lambda>x. r\<^sub>2 x / (ln x) + 2 / ln 2) \<in> rem_est c l"
unfolding rem_est_def
proof (rule sum_in_bigo)
  let ?O = "O(\<lambda>x. x * exp (- c * ln x ᣔ (1 / (1 + l))))"
  have "(\<lambda>x. r\<^sub>2 x / ln x) \<in> O(r\<^sub>2)"
  proof (rule bigoI, rule eventually_at_top_linorderI)
    fix x :: \<real> assume 1:"exp 1 \<le> x"
    have 2:"(0 :: \<real>) < exp 1" by simp
    hence 3:"0 < x" using 1 by linarith
    have 4: "0 \<le> \<bar>r\<^sub>2 x\<bar>" by auto
    have "(1 :: \<real>) = ln (exp 1)" by simp
    also have "\<dots> \<le> ln x" using 1 2 3 by (subst ln_le_cancel_iff)
    finally have "1 \<le> ln x" .
    thus "║r\<^sub>2 x / ln x║ \<le> 1 * ║r\<^sub>2 x║"
    by (auto simp add: field_simps, subst mult_le_cancel_right1, auto)
  qed
  also have "r\<^sub>2 \<in> ?O" by (fold rem_est_def, rule h)
  finally show "(\<lambda>x. r\<^sub>2 x / ln x) \<in> ?O" .
  have "(\<lambda>x :: \<real>. 2 / ln 2) \<in> O(\<lambda>x. x ᣔ (2/3))"
    by real_asymp
  also have "(\<lambda>x. x ᣔ (2/3)) \<in> ?O"
    using hl by (rule rem_est_1)
  finally show "(\<lambda>x :: \<real>. 2 / ln 2) \<in> ?O" .
qed

lemma PNT_2_imp_PNT_1:
  fixes l :: \<real>
  assumes h : "0 < l" and "PNT_2 l"
  shows "PNT_1 l"
unfolding PNT_1_def
proof -
  from \<open>PNT_2 l\<close> obtain c where h': "r\<^sub>2 \<in> rem_est c l" unfolding PNT_2_def r\<^sub>2_def by auto
  let ?a = "\<lambda>x. r\<^sub>2 x / ln x + 2 / ln 2"
  let ?b = "\<lambda>x. \<integral> {2..x} (\<lambda>t. r\<^sub>2 t / (t * (ln t)\<^sup>2))"
  have 1: "\<forall>\<^sub>F x in +\<infinity>. \<pi> x - Li x = ?a x + ?b x"
  by (rule eventually_at_top_linorderI, fold r\<^sub>1_def, rule lm_a3(2), blast)
  have 2: "(\<lambda>x. ?a x + ?b x) \<in> rem_est c l"
  by (unfold rem_est_def,
     (rule sum_in_bigo; fold rem_est_def),
     (rule lm_a5 lm_a4, rule h, rule h')+)
  show "\<exists>c. (\<lambda>x. \<pi> x - Li x) \<in> rem_est c l"
  proof
    show "(\<lambda>x. \<pi> x - Li x) \<in> rem_est c l"
      using landau_o.big.in_cong [OF 1] and 2
      unfolding rem_est_def by blast
  qed
qed

lemma PNT_3_imp_PNT_1:
  fixes l :: \<real>
  assumes h : "0 < l" and "PNT_3 l"
  shows "PNT_1 l"
using assms
  by (intro PNT_2_imp_PNT_1 PNT_3_imp_PNT_2)

unbundle no_prime_counting_notation

section \<open>Inequality of zeta function\<close>

lemma cos_inequality_1:
  fixes x :: \<real>
  shows "3 + 4*cos x + cos (2*x) \<ge> 0"
proof -
  have "cos (2*x) = (cos x)\<^sup>2 - (sin x)\<^sup>2"
    by (rule cos_double)
  also have "\<dots> = (cos x)\<^sup>2 - (1 - (cos x)\<^sup>2)"
    unfolding sin_squared_eq ..
  also have "\<dots> = 2 * (cos x)\<^sup>2 - 1" by auto
  finally have 1: "cos (2*x) = 2 * (cos x)\<^sup>2 - 1" .
  have "0 \<le> 2 * (1 + cos x)\<^sup>2" by auto
  also have "\<dots> = 3 + 4 * cos x + (2 * (cos x)\<^sup>2 - 1)"
    by (simp add: field_simps power2_eq_square)
  finally show ?thesis unfolding 1.
qed

notation zeta ("\<zeta>")
abbreviation "zeta_deriv s \<equiv> deriv \<zeta> s"
abbreviation "nat_power_abbrev n x \<equiv> (of_nat n) powr x"
notation nat_power_abbrev (infix "\<nat>ᣔ" 80)
abbreviation "mangoldt_complex :: _ \<Rightarrow> \<complex> \<equiv> mangoldt"
abbreviation "mangoldt_real :: _ \<Rightarrow> \<real> \<equiv> mangoldt"
notation mangoldt_complex ("\<Lambda>")
notation mangoldt_real ("\<Lambda>\<^sub>r")
notation zeta_deriv ("\<zeta>\<Zprime>")
notation fds_nth ("d\<^sub>n")
abbreviation "fds_zeta_complex :: \<complex> fds \<equiv> fds_zeta"
notation fds_zeta_complex ("\<zeta>\<^sub>d")
notation Suc ("_\<^sub>+" [101] 100)
notation fds_deriv ("d\<Zprime>")
notation Complex ("\<complex>")
abbreviation "log_zeta_deriv s \<equiv> \<zeta>\<Zprime> s / \<zeta> s"
notation log_zeta_deriv ("L\<zeta>\<Zprime>")

lemma
  assumes s: "Re s > 1"
  shows eval_fds_mongoldt:
    "eval_fds (fds \<Lambda>) s = - \<zeta>\<Zprime> s / \<zeta> s"
  and abs_conv_abscissa_mongoldt:
    "abs_conv_abscissa (fds \<Lambda>) \<le> 1"
  and abs_conv_mangoldt:
    "fds_abs_converges (fds \<Lambda>) s"
proof -
  have 1: "completely_multiplicative_function (d\<^sub>n \<zeta>\<^sub>d :: _ \<Rightarrow> \<complex>)" by standard auto
  moreover have "d\<^sub>n \<zeta>\<^sub>d 1 \<noteq> 0" by auto
  ultimately have "d\<^sub>n (d\<Zprime> \<zeta>\<^sub>d / \<zeta>\<^sub>d) n = -d\<^sub>n \<zeta>\<^sub>d n * \<Lambda> n" for n
    by (rule fds_nth_logderiv_completely_multiplicative)
  hence 2: "fds \<Lambda> = -(d\<Zprime> \<zeta>\<^sub>d / \<zeta>\<^sub>d)"
    by (intro fds_eqI, auto)
  have 3: "abs_conv_abscissa (d\<Zprime> \<zeta>\<^sub>d / \<zeta>\<^sub>d) \<le> 1"
    by (rule abs_conv_abscissa_completely_multiplicative_log_deriv
      [OF 1, unfolded abs_conv_abscissa_zeta], auto)
  hence 4: "abs_conv_abscissa (d\<Zprime> \<zeta>\<^sub>d / \<zeta>\<^sub>d) < ereal (s \<bullet> 1)"
    using s by (intro le_ereal_less, auto, unfold one_ereal_def, auto)
  have 5: "abs_conv_abscissa \<zeta>\<^sub>d < ereal (s \<bullet> 1)"
    using s by (subst abs_conv_abscissa_zeta, auto)
  hence 6: "fds_abs_converges (d\<Zprime> \<zeta>\<^sub>d / \<zeta>\<^sub>d) s"
    by (intro fds_abs_converges) (rule 4)
  from 2 have "eval_fds (fds \<Lambda>) s = eval_fds (-(d\<Zprime> \<zeta>\<^sub>d / \<zeta>\<^sub>d)) s" by auto
  also have "\<dots> = -eval_fds (d\<Zprime> \<zeta>\<^sub>d / \<zeta>\<^sub>d) s"
    by (intro eval_fds_uminus fds_abs_converges_imp_converges 6)
  also have "\<dots> = -(eval_fds (d\<Zprime> \<zeta>\<^sub>d) s / eval_fds \<zeta>\<^sub>d s)"
    using s by (subst eval_fds_log_deriv; ((intro 4 5)?, (auto intro!: eval_fds_zeta_nonzero)?))
  also have "\<dots> = - \<zeta>\<Zprime> s / \<zeta> s"
    using s by (subst eval_fds_zeta, blast, subst eval_fds_deriv_zeta, auto)
  finally show "eval_fds (fds \<Lambda>) s = - \<zeta>\<Zprime> s / \<zeta> s" .
  show "abs_conv_abscissa (fds \<Lambda>) \<le> 1"
    by (subst 2, subst abs_conv_abscissa_minus, rule 3)
  show "fds_abs_converges (fds \<Lambda>) s"
    by (subst 2, intro fds_abs_converges_uminus 6)
qed

lemma has_sum_summable [intro]:
  shows "has_sum f A x \<Longrightarrow> f summable_on A"
unfolding summable_on_def by auto

lemma sums_mangoldt:
  fixes s :: \<complex>
  assumes s: "Re s > 1"
  shows "has_sum (\<lambda>n. \<Lambda> n / n \<nat>ᣔ s) {1..} (- \<zeta>\<Zprime> s / \<zeta> s)"
proof -
  let ?f = "(\<lambda>n. \<Lambda> n / n \<nat>ᣔ s)"
  have 1: "fds_abs_converges (fds \<Lambda>) s"
    by (intro abs_conv_mangoldt s)
  hence 2: "fds_converges (fds \<Lambda>) s"
    by (rule fds_abs_converges_imp_converges)
  hence "summable (\<lambda>n. ║d\<^sub>n (fds \<Lambda>) n / nat_power n s║)"
    by (fold fds_abs_converges_def, intro 1)
  moreover have "(\<lambda>n. d\<^sub>n (fds \<Lambda>) n / nat_power n s) sums (- \<zeta>\<Zprime> s / \<zeta> s)"
    by (subst eval_fds_mongoldt(1) [symmetric], intro s, fold fds_converges_iff, intro 2)
  ultimately have "has_sum (\<lambda>n. d\<^sub>n (fds \<Lambda>) n / n \<nat>ᣔ s) UNIV (- \<zeta>\<Zprime> s / \<zeta> s)"
    by (fold nat_power_complex_def, rule norm_summable_imp_has_sum)
  moreover have [simp]: "(if n = 0 then 0 else \<Lambda> n) = \<Lambda> n" for n by auto
  ultimately have "has_sum ?f UNIV (- \<zeta>\<Zprime> s / \<zeta> s)" by (auto simp add: fds_nth_fds)
  hence 3: "has_sum ?f UNIV (- \<zeta>\<Zprime> s / \<zeta> s)" by auto
  have "sum ?f {0} = 0" by auto
  moreover have "has_sum ?f {0} (sum ?f {0})"
    by (rule has_sum_finite, auto)
  ultimately have "has_sum ?f {0} 0" by auto
  hence "has_sum ?f (UNIV - {0}) (- \<zeta>\<Zprime> s / \<zeta> s - 0)"
    by (intro has_sum_Diff 3, auto)
  moreover have "UNIV - {0 :: \<nat>} = {1..}" by auto
  ultimately show "has_sum ?f {1..} (- \<zeta>\<Zprime> s / \<zeta> s)" by auto
qed

lemma sums_Re_logderiv_zeta:
  fixes \<sigma> t :: \<real>
  assumes s: "\<sigma> > 1"
  shows "has_sum (\<lambda>n. \<Lambda>\<^sub>r n * n \<nat>ᣔ (-\<sigma>) * cos (t * ln n)) {1..} (Re (- \<zeta>\<Zprime> (\<complex> \<sigma> t) / \<zeta> (\<complex> \<sigma> t)))"
proof -
  have "Re (\<Lambda> n / n \<nat>ᣔ (\<complex> \<sigma> t)) = \<Lambda>\<^sub>r n * n \<nat>ᣔ (-\<sigma>) * cos (t * ln n)" if *: "1 \<le> n" for n
  proof -
    let ?n = "n :: \<complex>"
    have "1 / n \<nat>ᣔ (\<complex> \<sigma> t) = n \<nat>ᣔ (\<complex> (-\<sigma>) (-t))"
      by (fold powr_minus_divide, auto simp add: legacy_Complex_simps)
    also have "\<dots> = exp (\<complex> (-\<sigma> * ln n) (-t * ln n))"
      unfolding powr_def by (auto simp add: field_simps legacy_Complex_simps, use * in linarith)
    finally have "Re (1 / n \<nat>ᣔ (\<complex> \<sigma> t)) = Re \<dots>" by auto
    also have "\<dots> = n \<nat>ᣔ (-\<sigma>) * cos (t * ln n)"
      by (unfold powr_def, subst Re_exp, use * in auto)
    finally have 1: "\<Lambda>\<^sub>r n * Re (1 / n \<nat>ᣔ (\<complex> \<sigma> t)) = \<Lambda>\<^sub>r n * n \<nat>ᣔ (-\<sigma>) * cos (t * ln n)" by auto
    have rule_1: "Re (w * z) = Re w * Re z" if *: "Im w = 0" for z w :: \<complex> using * by auto
    have "Re (\<Lambda> n * (1 / n \<nat>ᣔ (\<complex> \<sigma> t))) = \<Lambda>\<^sub>r n * Re (1 / n \<nat>ᣔ (\<complex> \<sigma> t))"
      by (subst rule_1, auto)
    with 1 show ?thesis by auto
  qed
  note 1 = this
  show "has_sum (\<lambda>n. \<Lambda>\<^sub>r n * n \<nat>ᣔ (- \<sigma>) * cos (t * ln (real n)))
    {1..} (Re (- \<zeta>\<Zprime> (\<complex> \<sigma> t) / \<zeta> (\<complex> \<sigma> t)))"
    by (subst has_sum_cong, rule 1 [symmetric],
       (auto)[1], intro has_sum_Re sums_mangoldt,
       use s in auto)
qed

lemma logderiv_zeta_ineq:
  fixes \<sigma> t :: \<real>
  assumes s: "\<sigma> > 1"
  shows "3 * Re (L\<zeta>\<Zprime> (\<complex> \<sigma> 0)) + 4 * Re (L\<zeta>\<Zprime> (\<complex> \<sigma> t)) + Re (L\<zeta>\<Zprime> (\<complex> \<sigma> (2*t))) \<le> 0" (is "?x \<le> 0")
proof -
  have [simp]: "Re (-z) = - Re z" for z by auto
  have "has_sum (\<lambda>n.
      3 * (\<Lambda>\<^sub>r n * n \<nat>ᣔ (-\<sigma>) * cos (0 * ln n))
    + 4 * (\<Lambda>\<^sub>r n * n \<nat>ᣔ (-\<sigma>) * cos (t * ln n))
    + 1 * (\<Lambda>\<^sub>r n * n \<nat>ᣔ (-\<sigma>) * cos (2*t * ln n))
    ) {1..} (
      3 * Re (- \<zeta>\<Zprime> (\<complex> \<sigma> 0) / \<zeta> (\<complex> \<sigma> 0))
    + 4 * Re (- \<zeta>\<Zprime> (\<complex> \<sigma> t) / \<zeta> (\<complex> \<sigma> t))
    + 1 * Re (- \<zeta>\<Zprime> (\<complex> \<sigma> (2*t)) / \<zeta> (\<complex> \<sigma> (2*t)))
    )"
  by (intro has_sum_add has_sum_cmult_right sums_Re_logderiv_zeta s)
  hence *: "has_sum (\<lambda>n. \<Lambda>\<^sub>r n * n \<nat>ᣔ (-\<sigma>)
    * (3 + 4 * cos (t * ln n) + cos (2 * (t * ln n)))
    ) {1..} (-?x)"
  by (auto simp add: field_simps)
  have "-?x \<ge> 0"
  by (rule has_sum_nonneg, rule *,
     intro mult_nonneg_nonneg,
     auto intro: mangoldt_nonneg cos_inequality_1)
  thus "?x \<le> 0" by linarith
qed

section \<open>A lemma for non-zero region\<close>

notation field_differentiable (infix "#f\<Zprime>" 50)

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
    by (rule holomorphic_glue_to_analytic [
     where f = "\<lambda>z. f z / (z - \<xi>) ^ n"
       and g = g and S = "T' - {\<xi>}" and T = "ball \<xi> r"
       and U = S])
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

definition analytic_factor_p' where \<open>
analytic_factor_p' f S K \<equiv>
\<exists>g n. \<exists>\<alpha> :: \<nat> \<Rightarrow> \<complex>.
      g analytic_on S
    \<and> (\<forall>z \<in> K. g z \<noteq> 0)
    \<and> (\<forall>z \<in> S. f z = g z * (\<Prod>k<n. z - \<alpha> k))
    \<and> \<alpha> ` {..<n} \<subseteq> K\<close>

definition analytic_factor_p where \<open>
analytic_factor_p F \<equiv>
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
         "\<And>z. z \<in> S \<Longrightarrow> f z = f z * (\<Prod>k<(0 :: \<nat>). z - (\<lambda>_. 0) k)"
      by (rule af, use nz in auto)
    show "(\<lambda>k :: \<nat>. 0) ` {..<0} \<subseteq> K" by auto
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
    then obtain g n and \<alpha> :: "\<nat> \<Rightarrow> \<complex>"
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
obtains g n and \<alpha> :: "\<nat> \<Rightarrow> \<complex>" where
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

section \<open>Borel-Caratheodory theorem\<close>

theorem Schwarz_Lemma1:
fixes f :: "\<complex> \<Rightarrow> \<complex>"
  and \<xi> :: "\<complex>"
assumes "f holomorphic_on ball 0 1"
  and "f 0 = 0"
  and "\<And>z. ║z║ < 1 \<Longrightarrow> ║f z║ \<le> 1"
  and "║\<xi>║ < 1"
shows "║f \<xi>║ \<le> ║\<xi>║"
proof (cases "f constant_on ball 0 1")
  assume "f constant_on ball 0 1"
  thus ?thesis unfolding constant_on_def
    using assms by auto
next
  assume nc: "\<not>f constant_on ball 0 1"
  have "\<And>z. ║z║ < 1 \<Longrightarrow> ║f z║ < 1"
  proof -
    fix z :: \<complex> assume *: "║z║ < 1"
    have "║f z║ \<noteq> 1"
    proof
      assume "║f z║ = 1"
      hence "\<And>w. w \<in> ball 0 1 \<Longrightarrow> ║f w║ \<le> ║f z║"
        using assms(3) by auto
      hence "f constant_on ball 0 1"
        by (intro maximum_modulus_principle [where U = "ball 0 1" and \<xi> = z])
           (use * assms(1) in auto)
      thus False using nc by blast
    qed
    with assms(3) [OF *] show "║f z║ < 1" by auto
  qed
  thus "║f \<xi>║ \<le> ║\<xi>║" by (intro Schwarz_Lemma(1), use assms in auto)
qed

theorem Schwarz_Lemma2:
fixes f :: "\<complex> \<Rightarrow> \<complex>"
  and \<xi> :: "\<complex>"
assumes holf: "f holomorphic_on ball 0 R"
  and hR: "0 < R" and nz: "f 0 = 0"
  and bn: "\<And>z. ║z║ < R \<Longrightarrow> ║f z║ \<le> 1"
  and \<xi>R: "║\<xi>║ < R"
shows "║f \<xi>║ \<le> ║\<xi>║ / R"
proof -
  define \<phi> where "\<phi> z \<equiv> f (R * z)" for z :: \<complex>
  have "║\<xi> / R║ < 1" using \<xi>R hR by (subst nonzero_norm_divide, auto)
  moreover have "(f \<circ> (\<lambda>z. R * z)) holomorphic_on ball 0 1"
    by (rule holomorphic_on_compose, auto,
        rule holomorphic_on_subset, rule holf,
        fold scaleR_conv_of_real, use hR in auto)
  moreover have "\<phi> 0 = 0" unfolding \<phi>_def using nz by auto
  moreover have "\<And>z. ║z║ < 1 \<Longrightarrow> ║\<phi> z║ \<le> 1"
  proof -
    fix z :: \<complex> assume *: "║z║ < 1"
    have "║R*z║ < R" using hR * by (fold scaleR_conv_of_real) auto
    thus "║\<phi> z║ \<le> 1" unfolding \<phi>_def using bn by auto
  qed
  ultimately have "║\<phi> (\<xi> / R)║ \<le> ║\<xi> / R║"
    unfolding comp_def by (fold \<phi>_def, intro Schwarz_Lemma1)
  thus ?thesis unfolding \<phi>_def using hR by (subst (asm) nonzero_norm_divide, auto)
qed

theorem Borel_Caratheodory1:
assumes hr: "0 < R" "0 < r" "r < R"
    and f0: "f 0 = 0"
    and hf: "\<And>z. ║z║ < R \<Longrightarrow> Re (f z) \<le> A"
    and holf: "f holomorphic_on (ball 0 R)"
    and zr: "║z║ \<le> r"
  shows "║f z║ \<le> 2*r/(R-r) * A"
proof -
  have A_ge_0: "A \<ge> 0"
  using f0 hf by (metis hr(1) norm_zero zero_complex.simps(1))
  then consider "A = 0" | "A > 0" by linarith
  thus "║f z║ \<le> 2 * r/(R-r) * A"
  proof (cases)
    assume *: "A = 0"
    have 1: "\<And>w. w \<in> ball 0 R \<Longrightarrow> ║exp (f w)║ \<le> ║exp (f 0)║" using hf f0 * by auto
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
      also have "\<dots> = exp (0 :: \<real>)" by (subst f0) auto
      finally have "e = 0" by auto
      with \<open>e > 0\<close> show ?thesis by blast
    qed
    hence "f z = 0" using f0 hr zr unfolding constant_on_def by auto
    hence "║f z║ = 0" by auto
    also have "\<dots> \<le> 2 * r/(R-r) * A" using hr \<open>A \<ge> 0\<close> by auto
    finally show ?thesis .
  next
    assume A_gt_0: "A > 0"
    define \<phi> where "\<phi> z \<equiv> (f z)/(2*A - f z)" for z :: \<complex>
    have \<phi>_bound: "║\<phi> z║ \<le> 1" if *: "║z║ < R" for z
    proof -
      define u v where "u \<equiv> Re (f z)" and "v \<equiv> Im (f z)"
      hence "u \<le> A" unfolding u_def using hf * by blast
      hence "u\<^sup>2 \<le> (2*A-u)\<^sup>2" using A_ge_0 by (simp add: sqrt_ge_absD)
      hence "u\<^sup>2 + v\<^sup>2 \<le> (2*A-u)\<^sup>2 + (-v)\<^sup>2" by auto
      moreover have "2*A - f z = \<complex> (2*A-u) (-v)" by (simp add: complex_eq_iff u_def v_def)
      hence "║f z║\<^sup>2 = u\<^sup>2 + v\<^sup>2"
            "║2*A - f z║\<^sup>2 = (2*A-u)\<^sup>2 + (-v)\<^sup>2"
      unfolding u_def v_def using cmod_power2 complex.sel by presburger+
      ultimately have "║f z║\<^sup>2 \<le> ║2*A - f z║\<^sup>2" by auto
      hence "║f z║ \<le> ║2*A - f z║" by auto
      thus ?thesis unfolding \<phi>_def by (subst norm_divide) (simp add: divide_le_eq_1)
    qed
    moreover have nz: "\<And>z :: \<complex>. z \<in> ball 0 R \<Longrightarrow> 2*A - f z \<noteq> 0"
    proof
      fix z :: \<complex>
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
    ultimately have *: "║\<phi> z║ \<le> ║z║ / R"
      using hr(1) \<phi>_bound zr hr Schwarz_Lemma2 by auto
    also have "... < 1" using zr hr by auto
    finally have h\<phi>: "║\<phi> z║ \<le> r / R" "║\<phi> z║ < 1" "1 + \<phi> z \<noteq> 0"
    proof (safe)
      show "║\<phi> z║ \<le> r / R" using * zr hr(1)
        by (metis divide_le_cancel dual_order.trans nle_le)
    next
      assume "1 + \<phi> z = 0"
      hence "\<phi> z = -1" using add_eq_0_iff by blast
      thus "║\<phi> z║ < 1 \<Longrightarrow> False" by auto
    qed
    have "2*A - f z \<noteq> 0" using nz hr(3) zr by auto
    hence "f z = 2*A*\<phi> z / (1 + \<phi> z)"
      using h\<phi>(3) unfolding \<phi>_def by (auto simp add: field_simps)
    hence "║f z║ = 2*A*║\<phi> z║ / ║1 + \<phi> z║"
      by (auto simp add: norm_divide norm_mult A_ge_0)
    also have "\<dots> \<le> 2*A*(║\<phi> z║ / (1 - ║\<phi> z║))"
    proof -
      have "║1 + \<phi> z║ \<ge> 1 - ║\<phi> z║"
        by (metis norm_diff_ineq norm_one)
      thus ?thesis
        by (simp, rule divide_left_mono, use A_ge_0 in auto)
           (intro mult_pos_pos, use h\<phi>(2) in auto)
    qed
    also have "\<dots> \<le> 2*A*((r/R) / (1 - r/R))"
    proof -
      have *: "a / (1 - a) \<le> b / (1 - b)"
        if "a < 1" "b < 1" "a \<le> b" for a b :: \<real>
      using that by (auto simp add: field_simps)
      have "║\<phi> z║ / (1 - ║\<phi> z║) \<le> (r/R) / (1 - r/R)"
        by (rule *; (intro h\<phi>)?) (use hr in auto)
      thus ?thesis by (rule mult_left_mono, use A_ge_0 in auto)
    qed
    also have "\<dots> = 2*r/(R-r) * A" using hr(1) by (auto simp add: field_simps)
    finally show ?thesis .
  qed
qed

theorem Borel_Caratheodory2:
assumes hr: "0 < R" "0 < r" "r < R"
    and hf: "\<And>z. ║z║ < R \<Longrightarrow> Re (f z - f 0) \<le> A"
    and holf: "f holomorphic_on (ball 0 R)"
    and zr: "║z║ \<le> r"
  shows "║f z - f 0║ \<le> 2*r/(R-r) * A"
proof -
  define g where "g z \<equiv> f z - f 0" for z
  show ?thesis
  by (fold g_def, rule Borel_Caratheodory1)
     (unfold g_def, use assms in \<open>auto simp add: holomorphic_intros\<close>)
qed

definition "logderiv f x \<equiv> deriv f x / f x"
definition "log_differentiable f x \<equiv> (f #f\<Zprime> (at x)) \<and> f x \<noteq> 0"
notation has_derivative (infix "#d" 50)
notation has_field_derivative (infix "#fd" 50)
notation log_differentiable (infix "#l\<Zprime>" 50)

theorem logderiv_prod:
fixes f :: "'n \<Rightarrow> 'f \<Rightarrow> 'f :: real_normed_field"
assumes fin: "finite I"
    and lder: "\<And>i. i \<in> I \<Longrightarrow> f i #l\<Zprime> a"
  shows "logderiv (\<lambda>x. \<Prod>i\<in>I. f i x) a = (\<Sum>i\<in>I. logderiv (f i) a)" (is ?P)
    and "(\<lambda>x. \<Prod>i\<in>I. f i x) #l\<Zprime> a" (is ?Q)
proof -
  let ?a = "\<lambda>i. deriv (f i) a"
  let ?b = "\<lambda>i. \<Prod>j\<in>I - {i}. f j a"
  let ?c = "\<lambda>i. f i a"
  let ?d = "\<Prod>i\<in>I. ?c i"
  have der: "\<And>i. i \<in> I \<Longrightarrow> f i #f\<Zprime> (at a)"
    and nz: "\<And>i. i \<in> I \<Longrightarrow> f i a \<noteq> 0"
    using lder unfolding log_differentiable_def by auto
  have 1: "(*) x = (\<lambda>y. y * x)" for x :: 'f by auto
  have "((\<lambda>x. \<Prod>i\<in>I. f i x) #d
    (\<lambda>y. \<Sum>i\<in>I. ?a i * y *?b i)) (at a within UNIV)"
    by (rule has_derivative_prod, fold has_field_derivative_def)
       (rule field_differentiable_derivI, elim der)
  hence 2: "DERIV (\<lambda>x. \<Prod>i\<in>I. f i x) a :> (\<Sum>i\<in>I. ?a i * ?b i)"
    unfolding has_field_derivative_def
    by (simp add: sum_distrib_left [symmetric] mult_ac)
       (subst 1, blast)
  have prod_nz: "(\<Prod>i\<in>I. ?c i) \<noteq> 0"
    using prod_zero_iff nz fin by auto
  have mult_cong: "b = c \<Longrightarrow> a * b = a * c" for a b c :: \<real> by auto
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
assumes "f #l\<Zprime> a"
    and "g #l\<Zprime> a"
  shows "logderiv (\<lambda>z. f z * g z) a = logderiv f a + logderiv g a" (is ?P)
    and "(\<lambda>z. f z * g z) #l\<Zprime> a" (is ?Q)
proof -
  have "logderiv (\<lambda>z. f z * g z) a
      = logderiv (\<lambda>z. \<Prod>i\<in>{0, 1}. ([f, g]!i) z) a" by auto
  also have "\<dots> = (\<Sum>i\<in>{0, 1}. logderiv ([f, g]!i) a)"
    by (rule logderiv_prod(1), use assms in auto)
  also have "\<dots> = logderiv f a + logderiv g a"
    by auto
  finally show ?P .
  have "(\<lambda>z. \<Prod>i\<in>{0, 1}. ([f, g]!i) z) #l\<Zprime> a"
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
    and "(\<lambda>w. w - z) #l\<Zprime> a"
unfolding logderiv_def log_differentiable_def
  using assms by (auto simp add: derivative_intros)

theorem lemma_3_9_beta1:
fixes f M r s\<^sub>0
assumes zl: "0 < r" "0 \<le> M"
   and hf: "f holomorphic_on ball 0 r"
   and ne: "\<And>s. s \<in> ball 0 r \<Longrightarrow> f s \<noteq> 0"
   and bn: "\<And>s. s \<in> ball 0 r \<Longrightarrow> ║f s / f 0║ \<le> exp M"
 shows "║logderiv f 0║ \<le> 4 * M / r"
proof -
  obtain g
  where holg: "g holomorphic_on ball 0 r"
    and exp_g: "\<And>x. x \<in> ball 0 r \<Longrightarrow> exp (g x) = f x"
  by (rule holomorphic_logarithm_exists [of "ball 0 r" f 0]) (use zl(1) ne hf in auto)
  have f0: "exp (g 0) = f 0" using exp_g zl(1) by auto
  have "deriv f 0 = deriv (\<lambda>x. exp (g x)) 0"
  by (rule deriv_cong_ev, subst eventually_nhds)
     (rule exI [where x = "ball 0 (r / 2)"], use exp_g zl(1) in auto)
  also have "\<dots> = exp (g 0) * deriv g 0"
  by (intro DERIV_fun_exp [THEN DERIV_imp_deriv] field_differentiable_derivI)
     (meson holg open_ball zl(1) centre_in_ball holomorphic_on_imp_differentiable_at)
  finally have dg: "deriv f 0 / f 0 = deriv g 0"
  proof -
    assume *: "deriv f 0 = exp (g 0) * deriv g 0"
    have "f 0 \<noteq> 0" using ne zl(1) by auto
    thus ?thesis using * f0 by auto
  qed
  have "Re (g z - g 0) \<le> M" if *: "║z║ < r" for z
  proof -
    have "exp (Re (g z - g 0)) = ║exp (g z - g 0)║"
      by (rule norm_exp_eq_Re [symmetric])
    also have "\<dots> = ║f z / f 0║"
      by (subst exp_diff, subst f0, subst exp_g)
         (use * in auto)
    also have "\<dots> \<le> exp M" by (rule bn) (use * in auto)
    finally show ?thesis by auto
  qed
  hence "║g z - g 0║ \<le> 2 * (r / 2) / (r - r / 2) * M"
    if *: "║z║ \<le> r / 2" for z
    by (intro Borel_Caratheodory2 [where f = g])
       (use zl(1) holg * in auto)
  also have "\<dots> = 2 * M" using zl(1) by auto
  finally have "\<And>z. ║z║ \<le> r / 2 \<Longrightarrow> ║g z - g 0║ \<le> 2 * M" .
  hence "\<And>z. ║0 - z║ = r / 2 \<Longrightarrow> ║g z - g 0║ \<le> 2 * M" by auto
  moreover have "(\<lambda>z. g z - g 0) holomorphic_on cball 0 (r / 2)"
    by (rule holomorphic_on_subset [where s="ball 0 r"])
       (use zl(1) holg in \<open>auto simp add: holomorphic_intros\<close>)
  hence "(\<lambda>z. g z - g 0) holomorphic_on ball 0 (r / 2)"
        "continuous_on (cball 0 (r / 2)) (\<lambda>z. g z - g 0)"
    by (rule holomorphic_on_subset [where s="cball 0 (r / 2)"], auto)
       (rule holomorphic_on_imp_continuous_on, auto)
  ultimately have "║(deriv ^^ 1) (\<lambda>z. g z - g 0) 0║ \<le> fact 1 * (2 * M) / (r / 2) ^ 1"
    using zl(1) by (intro Cauchy_inequality) auto
  also have "\<dots> = 4 * M / r" by auto
  also have "deriv g 0 = deriv (\<lambda>z. g z - g 0) 0"
    by (subst deriv_diff, auto, rule holomorphic_on_imp_differentiable_at, use holg zl(1) in auto)
  hence "║deriv g 0║ = ║(deriv ^^ 1) (\<lambda>z. g z - g 0) 0║" by (auto simp add: derivative_intros)
  ultimately have "║deriv g 0║ \<le> 4 * M / r" by auto
  thus ?thesis unfolding logderiv_def by (subst dg)
qed

theorem lemma_3_9_beta2:
fixes f M r
assumes zl: "0 < r" "0 \<le> M"
   and af: "f analytic_on cball 0 r"
   and f0: "f 0 \<noteq> 0"
   and rz: "\<And>z. z \<in> cball 0 r \<Longrightarrow> Re z > 0 \<Longrightarrow> f z \<noteq> 0"
   and bn: "\<And>z. z \<in> cball 0 r \<Longrightarrow> ║f z / f 0║ \<le> exp M"
shows "- Re (logderiv f 0) \<le> 8 * M / r"
proof -
  have nz': "f not_zero_on cball 0 (r / 2)"
    unfolding not_zero_on_def using f0 zl(1) by auto
  obtain g n and \<alpha> :: "\<nat> \<Rightarrow> \<complex>"
  where ag: "g analytic_on cball 0 r"
    and ng: "\<And>z. z \<in> cball 0 (r / 2) \<Longrightarrow> g z \<noteq> 0"
    and fac: "\<And>z. z \<in> cball 0 r \<Longrightarrow> f z = g z * (\<Prod>k<n. (z - \<alpha> k))"
    and Im\<alpha>: "\<alpha> ` {..<n} \<subseteq> cball 0 (r / 2)"
    by (rule analytic_factorization [
      where K = "cball 0 (r / 2)"
        and S = "cball 0 r" and f = f])
       (use zl(1) af nz' in auto)
  have g0: "║g 0║ \<noteq> 0" using ng zl(1) by auto
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
  have "║g z / g 0║ \<le> exp M" if *: "z \<in> sphere 0 r" for z
  proof -
    let ?p = "║(\<Prod>k<n. (z - \<alpha> k)) / (\<Prod>k<n. (0 - \<alpha> k))║"
    have 1: "║f z / f 0║ \<le> exp M" using bn * by auto
    have 2: "║f z / f 0║ = ║g z / g 0║ * ?p"
      by (subst norm_mult [symmetric], subst (1 2) fac)
         (use that zl(1) in auto)
    have "?p = (\<Prod>k<n. (║z - \<alpha> k║ / ║0 - \<alpha> k║))"
      by (auto simp add: prod_norm [symmetric] norm_divide prod_dividef)
    also have "║z - \<alpha> k║ \<ge> ║0 - \<alpha> k║" if "k < n" for k
    proof (rule ccontr)
      assume **: "\<not> ║z - \<alpha> k║ \<ge> ║0 - \<alpha> k║"
      have "r = ║z║" using * by auto
      also have "... \<le> ║0 - \<alpha> k║ + ║z - \<alpha> k║" by (simp add: norm_triangle_sub)
      also have "... < 2 * ║\<alpha> k║" using ** by auto
      also have "\<alpha> k \<in> cball 0 (r / 2)" using Im\<alpha> that by blast
      hence "2 * ║\<alpha> k║ \<le> r" by auto
      finally show False by linarith
    qed
    hence "\<And>k. k < n \<Longrightarrow> ║z - \<alpha> k║ / ║0 - \<alpha> k║ \<ge> 1"
      using nz_\<alpha> by (subst le_divide_eq_1_pos) auto
    hence "(\<Prod>k<n. (║z - \<alpha> k║ / ║0 - \<alpha> k║)) \<ge> 1" by (rule prod_ge_1) simp
    finally have 3: "?p \<ge> 1" .
    have rule1: "b = a * c \<Longrightarrow> a \<ge> 0 \<Longrightarrow> c \<ge> 1 \<Longrightarrow> a \<le> b" for a b c :: \<real>
      by (metis landau_omega.R_mult_left_mono more_arith_simps(6))
    have "║g z / g 0║ \<le> ║f z / f 0║"
      by (rule rule1) (rule 2 3 norm_ge_zero)+
    thus ?thesis using 1 by linarith
  qed
  hence "\<And>z. z \<in> cball 0 r \<Longrightarrow> ║g z / g 0║ \<le> exp M"
    by (rule_tac maximum_modulus_frontier [where f = "\<lambda>z. g z / g 0" and S = "cball 0 r"])
       (use holg in auto)
  hence bn': "\<And>z. z \<in> cball 0 (r / 2) \<Longrightarrow> ║g z / g 0║ \<le> exp M" using zl(1) by auto
  have ag': "g analytic_on cball 0 (r / 2)"
    by (rule analytic_on_subset [where S = "cball 0 r"])
       (use ag zl(1) in auto)
  have "║logderiv g 0║ \<le> 4 * M / (r / 2)"
    by (rule lemma_3_9_beta1 [where f = g])
       (use zl ng bn' holg in auto)
  also have "\<dots> = 8 * M / r" by auto
  finally have bn_g: "║logderiv g 0║ \<le> 8 * M / r" unfolding logderiv_def by auto
  let ?P = "\<lambda>w. \<Prod>k<n. (w - \<alpha> k)"
  let ?S' = "\<Sum>k<n. logderiv (\<lambda>z. z - \<alpha> k) 0"
  let ?S = "\<Sum>k<n. - (1 / \<alpha> k)"
  have "g #f\<Zprime> at 0" using holg zl(1)
    by (auto intro!: holomorphic_on_imp_differentiable_at)
  hence ld_g: "g #l\<Zprime> 0" unfolding log_differentiable_def using g0 by auto
  have "logderiv ?P 0 = ?S'" and ld_P: "?P #l\<Zprime> 0"
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
  moreover have "Re ?S \<ge> 0"
  proof -
    have "0 \<le> Re (- (1 / \<alpha> k))" if *: "k < n" for k
    proof -
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
      thus ?thesis using Re_complex_div_le_0 by auto
    qed
    thus ?thesis by (auto intro: sum_nonneg)
  qed
  ultimately have "- Re (logderiv f 0) \<le> Re (- logderiv g 0)" by auto
  also have "\<dots> \<le> ║- logderiv g 0║" by (rule complex_Re_le_cmod)
  also have "\<dots> \<le> 8 * M / r" by simp (rule bn_g)
  finally show ?thesis .
qed

theorem lemma_3_9_beta3:
fixes f M r and s :: \<complex>
assumes zl: "0 < r" "0 \<le> M"
   and af: "f analytic_on cball s r"
   and f0: "f s \<noteq> 0"
   and rz: "\<And>z. z \<in> cball s r \<Longrightarrow> Re z > Re s \<Longrightarrow> f z \<noteq> 0"
   and bn: "\<And>z. z \<in> cball s r \<Longrightarrow> ║f z / f s║ \<le> exp M"
shows "- Re (logderiv f s) \<le> 8 * M / r"
proof -
  define g where "g \<equiv> f \<circ> (\<lambda>z. z + s)"
  have add_cball: "(\<lambda>z. z + s) ` cball 0 r = cball s r"
    unfolding cball_def dist_complex_def
  proof (auto cong: image_iff, rule_tac exI)
    fix x assume "║s - x║ \<le> r"
    thus "║-(s - x)║ \<le> r \<and> x = -(s - x) + s"
      by (auto simp only: norm_minus_cancel) auto
  qed
  hence 0: "g analytic_on cball 0 r"
    unfolding g_def using af
    by (intro analytic_on_compose) (auto simp add: analytic_intros)
  moreover have "g 0 \<noteq> 0" unfolding g_def using f0 by auto
  moreover have "(Re z > 0 \<longrightarrow> g z \<noteq> 0) \<and> ║g z / g 0║ \<le> exp M"
    if 1: "z \<in> cball 0 r" for z
  proof (intro impI conjI)
    assume 2: "0 < Re z"
    have "z + s \<in> cball s r" using 1 add_cball by auto
    moreover have "Re (z + s) > Re s" using 2 by auto
    ultimately show "g z \<noteq> 0" unfolding g_def comp_def using rz by auto
  next
    show "║g z / g 0║ \<le> exp M"
      unfolding g_def comp_def by (metis 1 add_0 imageI add_cball bn)
  qed
  ultimately have "- Re (logderiv g 0) \<le> 8 * M / r"
    by (intro lemma_3_9_beta2) (use zl in auto)
  thus ?thesis unfolding g_def logderiv_def using zl(1)
    by (subst (asm) deriv_chain)
       (auto simp add: derivative_intros
             intro!: analytic_on_imp_differentiable_at [OF af])
qed

locale \<zeta>_bound_param =
  fixes C T :: \<real>
    and \<theta> :: "\<real> \<Rightarrow> \<real>"
    and \<phi> :: "\<real> \<Rightarrow> \<real>"
    and region :: "\<complex> set"
  defines region: "region \<equiv>
      {z :: \<complex>. 1 - \<theta> (Im z) \<le> Re z \<and> Re z \<le> 2 \<and> Im z \<ge> T}"
  assumes
    T_pos: "0 \<le> T" and
    \<zeta>_bn: "\<And>z. z \<in> region \<Longrightarrow> ║\<zeta> z║ \<le> C * exp (-\<phi> (Im z))" and
    \<theta>_pos: "0 < \<theta> t \<and> \<theta> t \<le> 1" and
    \<phi>_pos: "0 < \<phi> t" and
    mo\<theta>: "antimono \<theta>" and
    mo\<phi>: "mono \<phi>" and
    asymp: "(\<lambda>t. \<phi> t / \<theta> t) \<in> o(exp \<circ> \<phi>)"

locale \<zeta>_bound_param1 = \<zeta>_bound_param +
  fixes \<sigma> \<gamma> r :: \<real> and s s' :: \<complex>
  assumes \<sigma>_cnd: "\<sigma> \<in> {1 + exp (- \<phi>(2 * \<gamma> + 1)) .. 2}"
      and \<gamma>_cnd: "\<gamma> \<ge> T + 1"
  defines r: "r \<equiv> \<theta> (2 * \<gamma> + 1)"

locale \<zeta>_bound_param2 = \<zeta>_bound_param1 +
  fixes \<delta> :: \<real>
  assumes \<delta>_cnd: "\<delta> = \<gamma> \<or> \<delta> = 2 * \<gamma>"
  defines s: "s \<equiv> \<complex> \<sigma> \<delta>"

locale \<zeta>_bound_param3 = \<zeta>_bound_param1 +
  defines s: "s \<equiv> \<complex> \<sigma> \<gamma>"
      and s': "s' \<equiv> \<complex> \<sigma> (2 * \<gamma>)"

context \<zeta>_bound_param2 begin
declare dist_complex_def [simp] norm_minus_commute [simp]

lemma cball_in_region:
  assumes "z \<in> cball s r"
  shows "1 - \<theta> (Im z) \<le> Re z"
proof -
  have 1: "r \<le> 1" unfolding r using \<theta>_pos by auto
  have "\<bar>Re (z - s)\<bar> \<le> ║z - s║" "\<bar>Im (z - s)\<bar> \<le> ║z - s║"
    by (rule abs_Re_le_cmod) (rule abs_Im_le_cmod)
  moreover have "║z - s║ \<le> r" using assms by auto
  ultimately have 2: "\<bar>Re z - \<sigma>\<bar> \<le> r" "\<bar>Im z - \<delta>\<bar> \<le> r" unfolding s by auto
  moreover have "\<delta> \<le> 2 * \<gamma>" using \<delta>_cnd \<gamma>_cnd T_pos by auto
  ultimately have "1 - \<theta> (Im z) \<le> 1 - \<theta> (2 * \<gamma> + \<theta> (2 * \<gamma> + 1))"
    unfolding r using mo\<theta> by (auto intro: antimonoD)
  also have "\<dots> \<le> 1 + exp (-\<phi> (2 * \<gamma> + 1)) - \<theta> (2 * \<gamma> + 1)"
  proof -
    from 1 have "2 * \<gamma> + \<theta> (2 * \<gamma> + 1) \<le> 2 * \<gamma> + 1"
      unfolding r by linarith
    hence "\<theta> (2 * \<gamma> + 1) - \<theta> (2 * \<gamma> + \<theta> (2 * \<gamma> + 1)) \<le> 0"
      using mo\<theta> by (auto intro: antimonoD)
    also have "0 \<le> exp (-\<phi> (2 * \<gamma> + 1))" by auto
    finally show ?thesis by auto
  qed
  also have "\<dots> \<le> \<sigma> - r" using \<sigma>_cnd unfolding r s by auto
  also have "\<dots> \<le> Re z" using 2 by auto
  finally show ?thesis .
qed

lemma logderiv_zeta_bound:
  shows "\<And>z. z \<in> cball s r \<Longrightarrow> ║L\<zeta>\<Zprime> z║ \<le> A * exp (\<phi> (2*\<gamma>+1))"
        "\<And>z. z \<in> cball s' r \<Longrightarrow> ║L\<zeta>\<Zprime> z║ \<le> A * exp (\<phi> \<gamma>)"
  sorry
end

context \<zeta>_bound_param begin
theorem zeta_nonzero_region1:
  shows "\<exists>A\<^sub>1. \<forall>s t. s \<ge> 1 - \<theta>(2*t+1) / \<phi>(2*t+1) \<longrightarrow> \<zeta> (\<complex> s t) \<noteq> 0"
  sorry
end
