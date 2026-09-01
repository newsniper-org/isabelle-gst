theory remove_syntax
imports "ZFC_in_HOL.ZFC_Typeclasses"
begin

(*Isabelle2026 port note.

  Mixfix templates in the HOL library now carry nested-cartouche markup
  (the "notation=..." / "indent=..." / "open_block ..." hints).  A
  'no_notation' or 'no_syntax' whose template does not match the
  declaration EXACTLY is SILENTLY IGNORED -- no warning, no error.  So
  every removal below is copied verbatim from the current library source,
  and any drift in a future release will again fail quietly.

  Where the library provides a declaration bundle, 'unbundle no X_syntax'
  is used instead: it is robust against template changes.  See
  isabelle/NEWS, "unbundle no foobar_syntax".*)

no_notation (ASCII)
  Not  (\<open>(\<open>open_block notation=\<open>prefix ~\<close>\<close>~ _)\<close> [40] 40) and
  conj  (infixr \<open>&\<close> 35) and
  disj  (infixr \<open>|\<close> 30) and
  implies  (infixr \<open>-->\<close> 25) and
  not_equal  (infix \<open>~=\<close> 50)

unbundle no funcset_syntax

no_translations
  "\<Pi> x\<in>A. B" \<rightleftharpoons> "CONST Pi A (\<lambda>x. B)"
  "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A"
no_syntax
  "_Pi" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"
    (\<open>(\<open>indent=3 notation=\<open>binder \<Pi>\<in>\<close>\<close>\<Pi> _\<in>_./ _)\<close> 10)
  "_lam" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
    (\<open>(\<open>indent=3 notation=\<open>binder \<lambda>\<in>\<close>\<close>\<lambda>_\<in>_./ _)\<close> [0, 0, 3] 3)

(*Hiding HOL set theory notation*)
no_notation
  Set.member  (\<open>'(\<in>')\<close>) and
  Set.member  (\<open>(\<open>notation=\<open>infix \<in>\<close>\<close>_/ \<in> _)\<close> [51, 51] 50) and
  Set.not_member  (\<open>'(\<notin>')\<close>) and
  Set.not_member  (\<open>(\<open>notation=\<open>infix \<notin>\<close>\<close>_/ \<notin> _)\<close> [51, 51] 50) and
  subset_eq  (\<open>'(\<subseteq>')\<close>) and
  subset_eq  (\<open>(\<open>notation=\<open>infix \<subseteq>\<close>\<close>_/ \<subseteq> _)\<close> [51, 51] 50) and
  Union (\<open>\<Union>\<close>) and Inter (\<open>\<Inter>\<close>) and
  union (infixl \<open>\<union>\<close> 65) and inter (infixl \<open>\<inter>\<close> 70) and
  image (infixr \<open>`\<close> 90)

(*ASCII ':' / '~:' for set membership: this is the collision that blocks
  the soft-type notation "x : P" of Soft_Types.thy.*)
unbundle no member_ASCII_syntax

no_notation (ASCII)
  less_eq  (\<open>'(<=')\<close>) and
  less_eq  (\<open>(\<open>notation=\<open>infix <=\<close>\<close>_/ <= _)\<close> [51, 51] 50) and
  union (infixl \<open>Un\<close> 65) and
  inter (infixl \<open>Int\<close> 70)

(*Hiding syntax and translations for HOL-set-bounded quantification*)
no_translations
  "\<forall>x\<in>A. P" \<rightleftharpoons> "CONST Ball A (\<lambda>x. P)"
  "\<exists>x\<in>A. P" \<rightleftharpoons> "CONST Bex A (\<lambda>x. P)"
no_syntax
  "_Ball"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<close>\<close>\<forall>(_/\<in>_)./ _)\<close> [0, 0, 10] 10)
  "_Bex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(\<open>indent=3 notation=\<open>binder \<exists>\<close>\<close>\<exists>(_/\<in>_)./ _)\<close> [0, 0, 10] 10)

(*Hiding syntax for HOL set comprehension notation*)
no_translations
  "{x. P}" \<rightleftharpoons> "CONST Collect (\<lambda>x. P)"
no_syntax
  "_Coll" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a set"    (\<open>(\<open>indent=1 notation=\<open>mixfix set comprehension\<close>\<close>{_./ _})\<close>)

(*'{x, y, z}' set enumeration*)
unbundle no set_enumeration_syntax

no_translations
  "\<Inter>x\<in>A. f" \<rightleftharpoons> "CONST Inter (Set.image (\<lambda>x. f) A)"
  "\<Union>x\<in>A. f" \<rightleftharpoons> "CONST Union (Set.image (\<lambda>x. f) A)"
  "\<Union>i<n. A" \<rightleftharpoons> "\<Union>i\<in>{..<n}. A"
no_syntax
  "_INTER"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set"  (\<open>(\<open>indent=3 notation=\<open>binder \<Inter>\<close>\<close>\<Inter>_\<in>_./ _)\<close> [0, 0, 10] 10)
  "_UNION"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'b set"  (\<open>(\<open>indent=3 notation=\<open>binder \<Union>\<close>\<close>\<Union>_\<in>_./ _)\<close> [0, 0, 10] 10)
(*'_UNION_less' lives in Set_Interval.thy, not Complete_Lattices.thy; it
  collides with the '\<Union>_<_. _' ordinal-indexed union of Ordinal/OrdRec.thy.*)
  "_UNION_less" :: "'a \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> 'b set"       (\<open>(\<open>indent=3 notation=\<open>binder \<Union>\<close>\<close>\<Union>_<_./ _)\<close> [0, 0, 10] 10)

no_notation Product_Type.Times (infixr \<open>\<times>\<close> 80)
no_translations
  "<x, y, z>"    \<rightleftharpoons> "<x, <y, z>>"
  "<x, y>"       \<rightleftharpoons> "CONST vpair x y"
  "<x, y, z>"    \<rightleftharpoons> "<x, <y, z>>"
  "\<lambda><x,y,zs>. b" \<rightleftharpoons> "CONST vsplit(\<lambda>x <y,zs>. b)"
  "\<lambda><x,y>. b"    \<rightleftharpoons> "CONST vsplit(\<lambda>x y. b)"
no_syntax (ASCII)
  "_Tuple"    :: "[V, Vs] \<Rightarrow> V"              (\<open><(_,/ _)>\<close>)
  "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   (\<open><_,/ _>\<close>)
no_syntax
  ""          :: "V \<Rightarrow> Vs"                    (\<open>_\<close>)
  "_Enum"     :: "[V, Vs] \<Rightarrow> Vs"             (\<open>_,/ _\<close>)
  "_Tuple"    :: "[V, Vs] \<Rightarrow> V"              (\<open>\<langle>(_,/ _)\<rangle>\<close>)
  "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   (\<open>\<langle>_,/ _\<rangle>\<close>)

(*Switch to using setminus character*)
no_notation
  Groups.minus (infixl \<open>-\<close> 65) and (*for set difference - perhaps use a different symbol?*)
  Groups.zero (\<open>0\<close>) and (*for the ordinal zero*)
  Groups.times (infixl \<open>*\<close> 70) (*for product soft-types*)

(*Removing syntax from Orderings.thy*)
no_translations
  "\<forall>x<y. P" \<rightharpoonup> "\<forall>x. x < y \<longrightarrow> P"
  "\<exists>x<y. P" \<rightharpoonup> "\<exists>x. x < y \<and> P"
no_syntax
  "_All_less" :: "[idt, 'a, bool] => bool"    (\<open>(\<open>indent=3 notation=\<open>binder \<forall>\<close>\<close>\<forall>_<_./ _)\<close>  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    (\<open>(\<open>indent=3 notation=\<open>binder \<exists>\<close>\<close>\<exists>_<_./ _)\<close>  [0, 0, 10] 10)
no_notation
  less_eq  (\<open>'(\<le>')\<close>) and
  less_eq  (\<open>(\<open>notation=\<open>infix \<le>\<close>\<close>_/ \<le> _)\<close>  [51, 51] 50) and
  less  (\<open>'(<')\<close>) and
  less  (\<open>(\<open>notation=\<open>infix <\<close>\<close>_/ < _)\<close>  [51, 51] 50)
(*The former removal of 'Orderings.ord_class.greater' used the template
  (\<open><\<close> 10), which matches no declaration in any release -- 'greater' is
  declared as (infix \<open>>\<close> 50).  It has always been a no-op; dropped rather
  than "fixed" into a removal nobody asked for.*)

no_notation ordLess2 (infix \<open><o\<close> 50)
no_notation cadd (infixl \<open>\<oplus>\<close> 65)

(*'\<bottom>' and '\<top>' are mixfix annotations on the CLASS PARAMETERS of
  'bot'/'top' (Orderings.thy), not part of the 'lattice_syntax' bundle that
  Main closes again -- so they remain active and collide with Soft_Types'
  empty type '\<bottom>' and universal type '\<top>'.*)
no_notation bot (\<open>\<bottom>\<close>)
no_notation top (\<open>\<top>\<close>)


end
