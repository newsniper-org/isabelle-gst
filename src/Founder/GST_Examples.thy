theory GST_Examples
  imports "../GST_Features"
begin

text \<open>The example GSTs of figure 4 of

  Dunne, Wells \<open>&\<close> Kamareddine, \<open>Generating Custom Set Theories with Non-Set
  Structured Objects\<close>, CICM 2021.

  That figure numbers the features 1 = \<open>Set\<close>, 3 = \<open>Pair\<close>, 5 = \<open>Nat\<close>,
  7 = \<open>Exception\<close>, and defines five GSTs over them:

  \<^item> \<open>ZF\<^sub>i := Base\<^sub>i + Iden\<^sub>i(1) + WF\<^sub>i(1)\<close>
  \<^item> \<open>ZFP\<^sub>i := Base\<^sub>i \<union> PTheory\<^sub>i + Iden\<^sub>i(1,3) + AllDistinct\<^sub>i(1,3) + WF\<^sub>i(1,3)\<close>
  \<^item> \<open>ZFN\<^sub>i := Base\<^sub>i \<union> NTheory\<^sub>i + Iden\<^sub>i(1,5) + AllDistinct\<^sub>i(1,5) + WF\<^sub>i(1)\<close>
  \<^item> \<open>ZFE\<^sub>i := \<dots> + Iden\<^sub>i(1,7) + AllDistinct\<^sub>i(1,7) + WF\<^sub>i(1) + ExOutside\<^sub>i(1)\<close>
  \<^item> \<open>ZF\<^sup>+\<^sub>i := \<dots> + Iden(1,3,5,7) + AllDistinct\<^sub>i(1,3,5,7) + WF\<^sub>i(1,5)
                + ExOutside\<^sub>i(1,5)\<close>

  \<^bold>\<open>Two different \<open>ZF\<^sup>+\<close>.\<close>  The later paper (Dunne \<open>&\<close> Wells,
  \<open>Isabelle/HOL/GST\<close>, 2022) uses the name \<open>ZF\<^sup>+\<close> for a different combination:
  \<open>\<section>1.5(10)\<close> there describes it as having "sets and all of the following as
  non-set objects: functions, ordinals, and the exception object".  That is
  the one already built in \<^theory>\<open>GST.GST_Features\<close> as \<^class>\<open>ZFplus\<close>, and it
  is the one theory \<open>Test\<close> builds a model for.  So the two papers'
  \<open>ZF\<^sup>+\<close> differ: the 2022 one carries \<^class>\<open>Ordinal\<close> and \<^class>\<open>Function\<close>
  where the 2021 one carries \<^class>\<open>Nat\<close>.  Both are kept -- the 2021 one is
  class \<open>ZFplus21\<close> below.

  Each class is produced by \<open>mk_gst\<close>, which generates it from the feature
  list: a cover axiom (the figure's \<open>Iden\<close>), pairwise disjointness of the
  feature logos (\<open>AllDistinct\<close>), cargo admit/restrict axioms (the role of
  \<open>ExOutside\<close>), and the \<open>otherwise\<close> axioms fixing each feature's default.

  A feature's \<open>blacklist\<close> names the features whose objects may not appear in
  its cargo, which is how \<open>ExOutside\<close> is expressed here.\<close>


subsection \<open>ZF -- every object is a set\<close>

ML \<open>val ZF_spec =
  [ {feat = GZF, default_val = \<^term>\<open>\<emptyset>\<close>, blacklist = []} ]\<close>

local_setup \<open>snd o mk_gst "ZF" ZF_spec\<close>

context ZF begin

text \<open>With \<open>Set\<close> as the only feature, \<open>Iden\<^sub>i(1)\<close> collapses to the statement
  that everything is a set -- the paper's remark that \<open>ZF\<^sub>i \<turnstile>\<^sub>i \<forall>\<^sub>i x. Set\<^sub>i x\<close>.\<close>

lemma everything_is_a_set : "x : Set"
  using fun_cong[OF cover_ax, of x]
  unfolding has_ty_def Any_def by simp

end


subsection \<open>ZFP -- sets and non-set ordered pairs\<close>

ML \<open>val ZFP_spec =
  [ {feat = GZF,   default_val = \<^term>\<open>\<emptyset>\<close>, blacklist = []},
    {feat = OPair, default_val = \<^term>\<open>\<emptyset>\<close>, blacklist = []} ]\<close>

local_setup \<open>snd o mk_gst "ZFP" ZFP_spec\<close>

context ZFP begin

lemma set_or_pair : "x : Set \<or> x : Pair"
  using fun_cong[OF cover_ax, of x]
  unfolding has_ty_def union_ty_def Any_def by simp

text \<open>\<open>AllDistinct\<^sub>i(1,3)\<close>: this is what makes \<open>\<langle>0,1\<rangle> \<noteq> {1,2}\<close> hold, which is
  the representation overlap the paper opens with.\<close>

lemma set_not_pair : "x : Set \<Longrightarrow> \<not> x : Pair"
  using fun_cong[OF GZF_OPair_disjoint, of x]
  unfolding has_ty_def inter_ty_def empty_typ_def by simp

end


subsection \<open>ZFN -- sets and non-set natural numbers\<close>

ML \<open>val ZFN_spec =
  [ {feat = GZF, default_val = \<^term>\<open>\<emptyset>\<close>, blacklist = []},
    {feat = Nat, default_val = \<^term>\<open>\<emptyset>\<close>, blacklist = []} ]\<close>

local_setup \<open>snd o mk_gst "ZFN" ZFN_spec\<close>

context ZFN begin

lemma set_or_nat : "x : Set \<or> x : Nat"
  using fun_cong[OF cover_ax, of x]
  unfolding has_ty_def union_ty_def Any_def by simp

lemma set_not_nat : "x : Set \<Longrightarrow> \<not> x : Nat"
  using fun_cong[OF GZF_Nat_disjoint, of x]
  unfolding has_ty_def inter_ty_def empty_typ_def by simp

end


subsection \<open>ZFE -- sets and an exception object outside every set\<close>

ML \<open>val ZFE_spec =
  [ {feat = GZF, default_val = \<^term>\<open>\<Zspot>\<close>, blacklist = [Exc]},
    {feat = Exc, default_val = \<^term>\<open>\<Zspot>\<close>, blacklist = []} ]\<close>

local_setup \<open>snd o mk_gst "ZFE" ZFE_spec\<close>

context ZFE begin

lemma set_or_exc : "x : Set \<or> x : Exc"
  using fun_cong[OF cover_ax, of x]
  unfolding has_ty_def union_ty_def Any_def by simp

lemma set_not_exc : "x : Set \<Longrightarrow> \<not> x : Exc"
  using fun_cong[OF GZF_Exc_disjoint, of x]
  unfolding has_ty_def inter_ty_def empty_typ_def by simp

text \<open>\<open>ExOutside\<^sub>i(1)\<close>: the exception object cannot be a member of any set.
  This is what \<open>blacklist = [Exc]\<close> on the \<open>Set\<close> feature buys -- it restricts
  \<open>Set\<close>'s cargo \<^term>\<open>SetMem\<close> away from \<^term>\<open>Exc\<close>.\<close>

lemma exc_outside_sets : "x : Exc \<Longrightarrow> \<not> x : SetMem"
  using fun_cong[OF restrict_cargo_GZF, of x]
  unfolding has_ty_def inter_ty_def empty_typ_def by simp

end


subsection \<open>ZF+ (2021) -- sets, non-set pairs, non-set naturals, exception\<close>

text \<open>\<^bold>\<open>Where this departs from the figure, and why.\<close>  The figure asks for
  \<open>ExOutside\<^sub>i(1,5)\<close>, i.e. the exception object is excluded from the internal
  structure of both sets \<open>(1)\<close> and naturals \<open>(5)\<close>.  Only the \<open>(1)\<close> half is
  stated below.

  The \<open>(5)\<close> half cannot be expressed through this development's blacklist
  mechanism: \<open>restrict_cargo\<close> asserts \<open>blacklisted \<triangle> cargo = \<bottom>\<close>, and the
  \<^class>\<open>Nat\<close> feature declares its cargo as \<^term>\<open>\<top>\<close>.  Blacklisting
  \<^term>\<open>Exc\<close> there would therefore assert \<open>Exc \<triangle> \<top> = \<bottom>\<close>, i.e. \<open>Exc = \<bottom>\<close>,
  which contradicts the \<^class>\<open>Exc\<close> axiom that \<^term>\<open>\<Zspot>\<close> satisfies it -- the
  class would be vacuous rather than merely weaker.

  This is a mismatch between the \<^class>\<open>Nat\<close> feature record and \<open>\<section>3.1\<close> of
  the 2022 paper, which says a feature's cargo "should be chosen as the soft
  type satisfied of all objects contained in the internal structure of some
  object".  Naturals have no internal structure -- the 2021 paper leaves
  \<open>child\<^sup>5\<^sub>i\<close> undefined -- so the faithful cargo is \<^term>\<open>\<bottom>\<close>, not \<^term>\<open>\<top>\<close>,
  and with \<^term>\<open>\<bottom>\<close> the restriction would hold vacuously as the figure
  intends.  Changing the shared \<^class>\<open>Nat\<close> record is out of scope here, so
  the weaker axiomatisation is used and the gap is recorded instead.\<close>

ML \<open>val ZFplus21_spec =
  [ {feat = GZF,   default_val = \<^term>\<open>\<Zspot>\<close>, blacklist = [Exc]},
    {feat = OPair, default_val = \<^term>\<open>\<Zspot>\<close>, blacklist = [Exc]},
    {feat = Nat,   default_val = \<^term>\<open>\<Zspot>\<close>, blacklist = []},
    {feat = Exc,   default_val = \<^term>\<open>\<Zspot>\<close>, blacklist = []} ]\<close>

local_setup \<open>snd o mk_gst "ZFplus21" ZFplus21_spec\<close>

context ZFplus21 begin

text \<open>\<open>Iden(1,3,5,7)\<close>.\<close>

lemma cover : "x : Set \<or> x : Pair \<or> x : Nat \<or> x : Exc"
  using fun_cong[OF cover_ax, of x]
  unfolding has_ty_def union_ty_def Any_def by simp

text \<open>\<open>AllDistinct\<^sub>i(1,3,5,7)\<close> -- all six pairs.\<close>

lemma all_distinct :
  "x : Set  \<Longrightarrow> \<not> x : Pair"
  "x : Set  \<Longrightarrow> \<not> x : Nat"
  "x : Set  \<Longrightarrow> \<not> x : Exc"
  "x : Pair \<Longrightarrow> \<not> x : Nat"
  "x : Pair \<Longrightarrow> \<not> x : Exc"
  "x : Nat  \<Longrightarrow> \<not> x : Exc"
  using fun_cong[OF GZF_OPair_disjoint, of x] fun_cong[OF GZF_Nat_disjoint, of x]
        fun_cong[OF GZF_Exc_disjoint, of x] fun_cong[OF OPair_Nat_disjoint, of x]
        fun_cong[OF OPair_Exc_disjoint, of x] fun_cong[OF Nat_Exc_disjoint, of x]
  unfolding has_ty_def inter_ty_def empty_typ_def by simp_all

text \<open>\<open>ExOutside\<^sub>i(1)\<close>, and the same for pairs.\<close>

lemma exc_outside_sets : "x : Exc \<Longrightarrow> \<not> x : SetMem"
  using fun_cong[OF restrict_cargo_GZF, of x]
  unfolding has_ty_def inter_ty_def empty_typ_def by simp

lemma exc_outside_pairs : "x : Exc \<Longrightarrow> \<not> x : PairMem"
  using fun_cong[OF restrict_cargo_OPair, of x]
  unfolding has_ty_def inter_ty_def empty_typ_def by simp

end

end
