Require Import QuickChick SetOfOutcomes.

Require Import Common Machine Indist Generation GenerationProofsHelpers. 

Require Import List.
Require Import ZArith.  
Require Import EquivDec.

Require Import ssreflect ssrbool ssrnat eqtype.


Lemma gen_from_length_correct: forall l,
  (gen_from_length l) <--> (fun z => (Z.le 0 z /\ Z.le z (l-1))).
Proof.
  move => l z. rewrite /gen_from_length choose_def. 
  split => [[/Z.compare_le_iff H1 /Z.compare_ge_iff H2]|
            [/Z.compare_le_iff H1 /Z.compare_ge_iff H2]];
    by split; auto.
Qed.

Lemma gen_from_nat_length_correct: forall l,
  (gen_from_nat_length l) <--> (fun z => (Z.le 0 z /\ Z.le z ((Z.of_nat l)-1))).
Proof.
  move => l z.
  rewrite /gen_from_nat_length. 
  move/(_ (Z.of_nat l)): gen_from_length_correct; apply. 
Qed.

Lemma gen_BinOpT_correct : 
  peq gen_BinOpT all.
Proof.
  rewrite /gen_BinOpT /all. move => op. 
  split => // _.  
  apply oneof_equiv. left. 
  case : op; [exists (pure BAdd) | exists (pure BMult)]; split => //=;
  [|right]; by left.
Qed.

Lemma gen_label_correct : 
  forall (l : Label),
    (gen_label l) <--> (fun e => In e (allThingsBelow l)).
Proof.
  move=> l. rewrite /gen_label. move => l'. 
  split => [/elements_equiv [H1 | [H1 H2]] //= | HIn]; subst.   
  + rewrite /allThingsBelow  /allBelow in H1. apply map_eq_nil in H1.
    by move/powerset_nonempty : H1.
  + apply elements_equiv. by left.
Qed.

Section WithDataLenNonEmpty.

Variable inf : Info.
Hypothesis data_len_nonempty : data_len inf <> [].


Lemma gen_label_inf_correct :
  (gen_label_inf inf) <--> (fun e => In e (allThingsBelow (top_prin inf))).
Proof.
  apply/gen_label_correct.
Qed.

(* PC *)

Definition PC_spec (pc : Ptr_atom) :=
  let '(PAtm z l) := pc in
  (In l (allThingsBelow (top_prin inf))) /\ 
  (0 <= z <= (code_len inf) - 1)%Z.

Lemma gen_PC_correct: 
  (gen_PC inf) <--> PC_spec.
Proof. 
  move=> ptr. rewrite /gen_PC /smart_gen /smart_gen_label.
  split.
  + rewrite bindGen_def. move => [lab [gen_lab H]]. 
    move/gen_label_inf_correct: gen_lab.
    rewrite bindGen_def in H. 
    move : H => [z [/gen_from_length_correct H1 Hret]].
    rewrite returnGen_def in Hret. subst. by split.
  + case : ptr => z l. move => [Hin Hrng]. 
    rewrite bindGen_def. exists l; split.
    by apply /gen_label_inf_correct.
    rewrite bindGen_def. exists z; split => //.
    by apply /gen_from_length_correct.
Qed.


(* Pointer *)
Definition Pointer_spec (ptr : Pointer) :=
  let '(Ptr mf addr) := ptr in
  (exists len, In (mf, len) (data_len inf) /\ 
               (0 <= addr <= len - 1)%Z). 

Lemma gen_Pointer_correct: 
    (gen_Pointer inf) <--> Pointer_spec.                        
Proof. 
  move => ptr. remember inf as Inf.
  destruct Inf.
  rewrite /gen_Pointer.
  split.
  * rewrite bindGen_def. move => [[mf z] [/elements_equiv Helem  H]].
    rewrite bindGen_def in H. move : H => [a [/gen_from_length_correct H Hret]].
    rewrite returnGen_def in Hret. subst ptr.
    simpl. case : Helem => [HIn | [Heq1 [Heq2 Heq3]]].
    - exists z. split => //. rewrite -HeqInf. assumption. 
    - by subst.
  * case: ptr => mf z.
    destruct data_len as [| x xs].
    - rewrite bindGen_def. 
      move=> [len  [//= HIn Hrng]].
    -  Opaque bindGen choose Z.compare returnGen. 
       move=> [len  [//= HIn [Hrng1 Hrng2]]].
       rewrite bindGen_def.  
       exists (mf, len). split.
       apply/elements_equiv. 
       by left; rewrite -HeqInf in HIn. 
       rewrite bindGen_def. 
       exists z. split => //. split. by apply/Z.compare_le_iff. 
       by apply/Z.compare_ge_iff.
Qed.

(* Value *)

Definition val_spec (inf : Info) (v : Value) :=
  match v with 
    | Vint _ => True
    | Vptr ptr =>
      let '(Ptr mf addr) := ptr in
      (exists len, In (mf, len) (data_len inf) /\ 
                   (0 <= addr <= len - 1)%Z) 
    | Vcptr z => (0 <= z <= (code_len inf) - 1)%Z
    | Vlab l => In l (allThingsBelow (top_prin inf))
  end.


Lemma gen_value_correct:  
    (gen_Value inf) <--> (val_spec inf).
Proof. 
  rewrite /gen_Value /val_spec.  
  clear data_len_nonempty. remember inf as Inf.
  case : Inf HeqInf => def clen dlen top reg HeqInf. case; rewrite !HeqInf.
  + (* VInt *) 
    move => z. split => // _. apply/frequency_equiv.
    left. exists 1. eexists. split. by constructor.
    split => //.
    rewrite liftGen_def. eexists; split => //.
    apply/frequency_equiv. left.
    exists 10. exists arbitrary. split. by constructor.
    split => //. by apply/arbInt_correct.
  + (* Vptr *)  
    case => mf addr.   
    split. Opaque bindGen choose Z.compare returnGen gen_Pointer.    
    - move/frequency_equiv => [[n [ g [H1 [H2 H3]]]] | [[// | H1] H2]]. 
      * case:H1 => [[Heq1 Heq2] | [[Heq1 Heq2] | 
                                   [[Heq1 Heq2] | [[Heq1 Heq2] | //]]]];
        subst n g; try (subst Heq1 Heq2);
        try (rewrite liftGen_def in H2; move : H2 => [a [H2 H2']]);
        try discriminate.  
        move/gen_Pointer_correct: H2 H2' => H2 [H2']; subst.
        move : H2 => //= [len [ HIn Hrng]]. exists len. split => //.
        by rewrite -HeqInf in HIn.
      * by rewrite liftGen_def in H2; move : H2 => [a [H2 H2']].
    - move => [len [HIn [Hrng1 Hrg2]]].
      apply/frequency_equiv. left. exists 1. eexists. 
      split. apply in_cons.  apply in_cons. constructor. 
      reflexivity.
      rewrite liftGen_def. split => //. eexists.
      split => //. 
      apply gen_Pointer_correct. exists len. split => //.
   + (* Vcptr *)
     move => addr. split. 
     - move/frequency_equiv => [[n [g [H1 [H2 H3]]]] | [H1 H2]]. 
       * case: H1 => [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | //]]]];
         subst; try (rewrite liftGen_def in H2; move : H2 => [a [H2 H2']]); 
         try discriminate.
         move : H2 H2' => [/Z.compare_le_iff H1 /Z.compare_ge_iff H2] [H2']; subst.
         by split.
       * by rewrite liftGen_def in H2; move : H2 => [a [H2 H2']].
     - move => [/=  H1  H2].
       apply/frequency_equiv. left. exists 1. eexists. split. 
       apply in_cons. constructor. 
       reflexivity. 
       rewrite liftGen_def. split => //. exists addr. split => //=. 
       split. by apply/Z.compare_le_iff. 
       rewrite -HeqInf /= in H2.
       by apply/Z.compare_ge_iff.
   + (* Vlab *)
     move => L. split.
     - move/frequency_equiv => [[n [g [H1 [H2 H3]]]] | [H1 H2]].
       * case: H1 => [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | [[Heq1 Heq2] | //]]]];
         subst g n; try (rewrite liftGen_def in H2; move : H2 => [a [H2 H2']]);
         try discriminate.  
         by move : H2 H2' => /gen_label_inf_correct H1 [H2']; subst.
       * by rewrite liftGen_def in H2; move : H2 => [a [H2 H2']].
     - move => H. apply/frequency_equiv. left. exists 1. eexists.
       split. apply in_cons. apply in_cons. apply in_cons. constructor. 
       reflexivity.
       rewrite liftGen_def. split => //. exists L. split => //=.
       by apply/gen_label_inf_correct.
Qed.
      
(* Atom *) 

Definition atom_spec inf atm  := 
  let '(Atm val lab) := atm in
  val_spec inf val /\ 
  In lab (allThingsBelow (top_prin inf)).
       
Lemma gen_atom_correct:
    (gen_atom inf) <--> (atom_spec inf).
Proof.
  move => atm. rewrite /gen_atom /liftGen2 bindGen_def. case: atm => val lab. 
  split. 
  + move => [val' [/gen_value_correct Hval Hbind]].
    rewrite bindGen_def in Hbind.
    move : Hbind => [lab' [/gen_label_inf_correct Hlab Hret]].
    rewrite returnGen_def in Hret. 
    by move : Hret => [Heq1 Heq2]; subst.
  + move => [Hval Hlab].
    exists val. split; [by apply/gen_value_correct| ].
    rewrite bindGen_def. exists lab. split => //.
    by apply/gen_label_inf_correct.
Qed.
  
(* regSet  *)

Definition regs_spec inf regs :=
  (length regs = no_regs inf) /\
  (forall reg, 
     In reg regs ->
     let '(Atm val lab) := reg in
     val_spec inf val /\ 
     In lab (allThingsBelow (top_prin inf))).

Lemma gen_registers_correct:
  (gen_registers inf) <--> (regs_spec inf).
Proof.    
  move => regs. 
  rewrite /gen_registers. split.
  + move /vectorOf_equiv => [H1 H2].
    split => //. move => reg HIn. by apply/gen_atom_correct; apply H2. 
  + move => [Hlen Hregs]. apply/vectorOf_equiv. split => // x HIn.
    apply/gen_atom_correct. by apply Hregs.
Qed.

(* stack_loc *)

Definition stack_loc_spec (inf : Info) g (l1 l2: Label) t : Prop:=
  let '(ptr_a, lab, regs, ptr_r) := t in
  In lab (allThingsBelow (top_prin inf)) /\
  regs_spec inf regs /\
  (0 <= ptr_r <= (Z.of_nat (no_regs inf) - 1))%Z /\
  let 'PAtm addr lab' := ptr_a in
  (0 <= addr <= ((code_len inf) - 1))%Z /\
  g l1 l2 lab'.

Lemma gen_stack_loc_correct :
  forall f g l1 l2, 
    (f l1 l2) <--> (g l1 l2) ->
    (smart_gen_stack_loc f l1 l2 inf) <--> (stack_loc_spec inf g l1 l2).
Proof.
  move=> f g l1 l2 Hequiv. 
  rewrite /smart_gen_stack_loc /smart_gen /bindGen /returnGen 
          /PredMonad /bindP /returnP //=.
  move => [[[ptr_a lab] regs] ptr_r]. split.
  + move =>  
    [regs' [/gen_registers_correct Hregs 
             [ptr_a' [[lab' [/gen_label_inf_correct Hlab H']]
                      [z [[/Z.compare_le_iff H1 /Z.compare_ge_iff H2] H]]]]]].
    move: H => [a [/gen_label_inf_correct Hlab' [lab'' [fl1l2 Hret]]]].
    case: ptr_a' lab' Hret Hlab H' => addr_a' lab_a' lab' Hret' Hlab H'.
    move : Hret' => [Heq1 Heq2 Heq3 Heq4]; subst.
    rewrite  /bindGen /returnGen /PredMonad /bindP /returnP //= in H'.
    move: H' => [z' [[/Z.compare_le_iff H1' /Z.compare_ge_iff H2'] [Heq1 Heq2]]]; subst.
    repeat (split  => //=; by auto). split => //=. split => //=. split => //=.
    split => //=. auto. auto. by apply Hequiv.
  + case: ptr_a. move => addr_a l_a [H1 [H2 [[H3 H3'] [[H4 H5] H6]]]].
    eexists; split. by apply/gen_registers_correct. 
    eexists; split. exists lab. split.
    by apply /gen_label_inf_correct.
    rewrite bindGen_def. 
    exists addr_a. split. 
    split. by apply/Z.compare_le_iff. 
    by apply/Z.compare_ge_iff. rewrite returnGen_def. reflexivity.
    exists ptr_r. split. split. 
    by apply/Z.compare_le_iff. by apply/Z.compare_ge_iff.
    exists lab. split. by apply /gen_label_inf_correct.
    exists l_a. split => //=. by apply Hequiv.
Qed.
   
(* gen_label_between_lax *)

Lemma gen_label_between_lax_correct :
  forall l1 l2,
    (gen_label_between_lax l1 l2) <--> (fun l => 
                                          (l1 <: l /\ In l (allThingsBelow l2))
                                          \/ l = l2 /\ l1 <: l2 = false).
Proof.
  move => l1 l2 l.  rewrite /gen_label_between_lax. split. 
  + move/elements_equiv => [ /filter_In [H1 H2] | 
                             [/filter_nil [/allThingsBelow_nonempty //| H1] H2]]. subst.  
    by left. 
    right. split => //=. apply H1. 
    rewrite /allThingsBelow /allBelow. (* Search _ (map _ _) In. *)
    rewrite -[X in In X _]label_of_list__elements. apply in_map.
    by apply powerset_in_refl.
  + move => [[H1 H2] | [H1 H2]]; subst; apply elements_equiv.
    by left; apply filter_In.
    right.  split => //. apply filter_nil.  
    right => x /allThingsBelow_isLow In.
    remember (l1 <: x) as b. symmetry in Heqb. case: b Heqb => heqb //.
    have H : l1 <: l2 = true by eapply flows_trans; eauto.
    congruence. 
Qed.

Definition gen_label_between_lax_spec (l1 l2 l: Label) : Prop := 
  (l1 <: l /\ l <: l2) \/ l = l2 /\ l1 <: l2 = false.


Lemma gen_label_between_lax_correct_admited :
  forall l1 l2,
    (gen_label_between_lax l1 l2) <--> (gen_label_between_lax_spec l1 l2).
Proof.
  move => l1 l2 l.  rewrite /gen_label_between_lax. split. 
  + move/elements_equiv => [ /filter_In [H1 H2] | 
                             [/filter_nil [/allThingsBelow_nonempty //| H1] H2]]; subst.  
    - left; split => //. by apply/allThingsBelow_isLow.
    - right. split => //=. apply H1. 
      rewrite /allThingsBelow /allBelow.
      rewrite -[X in In X _]label_of_list__elements. apply in_map.
        by apply powerset_in_refl.
  + move => [[H1 H2] | [H1 H2]]; subst; apply elements_equiv.
    left. apply filter_In. split => //.
    by apply/allThingsBelow_isLow'.  (* Here is the admited part *)
    right. split => //. apply filter_nil.  
    right => x /allThingsBelow_isLow In. 
    remember (l1 <: x) as b. symmetry in Heqb. case: b Heqb => heqb //.
    have H : l1 <: l2 = true by eapply flows_trans; eauto.
    congruence.  
Qed.

(* Stack *)

Definition stack_spec (pc: Ptr_atom) inf (s: Stack) : Prop :=
  s = Mty \/ 
  exists loc, s = loc ::: Mty /\ 
              stack_loc_spec inf gen_label_between_lax_spec bot ∂pc loc.

Lemma gen_stack_correct: 
  forall (pc: Ptr_atom),
    (smart_gen_stack pc inf) <--> (stack_spec pc inf). 
Proof.
  Opaque smart_gen_stack_loc.
  rewrite /smart_gen_stack /stack_spec. move => pc st.
  split. 
  + move/frequency_equiv => [[n [gen [[[Heq1 Heq2] | [[Heq1 Heq2] | //]] [Hg Hneq]]]] | 
                             [[H1 //= | H1] H2]]; subst.
    by left; rewrite Hg. 
    rewrite bindGen_def in Hg. move: Hg => [loc (* [[[ptr_a l] regs] reg_ptr] *) 
                                              [/gen_stack_loc_correct H1 H2]].
    rewrite returnGen_def in H2. subst. right.
    exists loc.  split => //. apply H1.
    apply gen_label_between_lax_correct_admited.
    by left; rewrite H2. 
  +  move => [Heq | H]; subst; apply frequency_equiv.
     - left; eexists; eexists; split. by constructor. by split => //.
     - case: st H => [H |loc st [loc' [[H1] H2]]]; left; eexists; eexists; split; subst.
       * by constructor. by split => //.
       * by apply in_cons; constructor. 
         rewrite bindGen_def. split => //. exists loc'.
         split => //. eapply gen_stack_loc_correct.
         by apply (gen_label_between_lax_correct_admited ⊥ ∂(pc)).
         assumption.
Qed.

(* frame *)    

Definition mem_single_upd_spec (inf : Info) mem mf (mem' : memory) := 
  match Mem.get_frame mem mf with 
    | Some (Fr stamp lab data) => 
      exists fr, Mem.upd_frame mem mf fr = Some mem' /\
                 let 'Fr stamp' lab' data' := fr in 
                 lab' = lab /\ stamp' = stamp /\ 
                 length data' = length data /\ 
                 forall atm, In atm data' -> atom_spec inf atm
    | None => mem' = mem
  end. 
  

Lemma populate_frame_correct : 
  forall mem mf,
    (populate_frame inf mem mf) <--> (mem_single_upd_spec inf mem mf).
Proof. 
  move=> mem mf mem'.  rewrite /populate_frame /mem_single_upd_spec.
  remember (Mem.get_frame mem mf) as opt. 
  case: opt Heqopt => [fr | ] Heqopt. 
  case: fr Heqopt => stamp lab data Heq. 
  - rewrite bindGen_def. 
    symmetry in Heq. move/Mem.upd_get_frame : (Heq) => Hupd.
    split. 
    + move => [atmlst [/vectorOf_equiv [Hl Hvec] Hmatch]]. 
      move/(_ (Fr stamp lab atmlst)): Hupd => [fr Hfr].
      rewrite Hfr returnGen_def in Hmatch; subst.
      exists (Fr stamp lab atmlst). repeat split => //.
      move => atm HIn. apply/gen_atom_correct. by apply Hvec.
    + move => [fr [Hget H]]. 
      case: fr Hupd Hget H => 
        stamp' lab' data' Hupd Hget [Heq1 [Heq2 [Heq3 H]]]; subst.
      exists data'. split. 
      apply/vectorOf_equiv. split => // x HIn. by apply/gen_atom_correct; eauto.
      by rewrite Hget.
  - by rewrite /pure returnGen_def.
Qed.

(* Memory *)

Lemma zreplicate_spec : 
  forall {A} (v : A) (z : Z),
    (0 <= z)%Z ->
    exists (l : list A), 
      (forall x, In x l -> x = v) /\
      length l = Z.to_nat z /\
      zreplicate z v = Some l.
Proof.
  move => A v z Hle. exists (replicate (Z.to_nat z) v). 
  repeat split.
  - move=> x HIn. apply Z2Nat.inj_le in Hle; try omega.
    induction (Z.to_nat z) as [| n IHn].
    + contradiction.
    + destruct HIn as [Heq | HIn]; try (symmetry; assumption). 
      apply IHn; auto; simpl; omega. 
  - apply Z2Nat.inj_le in Hle; try omega.
    induction (Z.to_nat z) as [| n IHn].
    + reflexivity.
    + simpl. rewrite IHn; auto; simpl; omega.
  - rewrite /zreplicate. destruct (Z_lt_dec z 0); try reflexivity.
    omega.
Qed.

Lemma zreplicate_eq :
  forall {A} (l: list A) v z,
    (0 <= z)%Z ->
    (forall x, In x l ->  x = v) ->
    length l = Z.to_nat z ->
    zreplicate z v = Some l.
Proof.
  move => A l v x Hle HIn Heq.
  rewrite /zreplicate. destruct ( Z_lt_dec x 0 ) as [H | H].
  - omega.
  - apply Z2Nat.inj_le in Hle; try omega.
    clear H Hle. generalize dependent l. induction (Z.to_nat x) as [| n IHn].
    + simpl. intros l. destruct l; try discriminate. reflexivity.
    + simpl. intros l HIn Hlen. apply f_equal. destruct l; try discriminate.
      rewrite (HIn a (in_eq a l)). apply f_equal.
      inversion Hlen as [Hlen'].
      assert (Hsome: Some (replicate n v) = Some l).
      { apply IHn; auto. intros x' HIn'. apply HIn. apply in_cons.
        assumption. } rewrite Hlen'.
      inversion Hsome. reflexivity.
Qed.


Lemma get_all_blocks_no_dubs : 
  forall (m : memory) b l, In b (Mem.get_all_blocks l m) -> 
                count_occ (Mem.EqDec_block) (Mem.get_all_blocks l m) b = 1.


Definition init_mem_spec (top : Label) (m : memory) :=
  forall b l st data, 
    Mem.get_frame m b = Some (Fr st l data) ->
    In l (allThingsBelow top) /\
    (C.min_frame_size <= Z.of_nat (length data) <= C.max_frame_size)%Z /\
    st = bot /\ Mem.stamp b = bot. 


Lemma gen_init_mem_helper_correct :
  forall (top : Label) (n: nat) (m : memory),
    (init_mem_spec top m) -> 
    (gen_init_mem_helper top n m) <--> 
    (fun m' => 
       (exists (lst : list (Label * (list Atom))),
          length lst = n /\ 
          (forall l data, 
             In (l, data) lst -> 
             (C.min_frame_size <= Z.of_nat (length data) <= C.max_frame_size)%Z /\
             In l (allThingsBelow top) /\
             (forall v, In v data ->  v = (Vint 0 @ bot)) 
          ) /\
          m' = fold_left 
                 (fun (m_i : memory) (elem : Label * (list Atom))  =>
                    let '(l, data) := elem in
                    let (_, m) := Mem.alloc Local m_i bot (Fr bot l data) in m) lst m) /\ 
       init_mem_spec top m'
    ).
Proof.
  move => top n m Hspec m'. split. 
  { move => Hgen. generalize dependent m. 
      induction n as [| n IHn]; intros mem Hspec Hgen.
      - simpl in *. inv Hgen. split => //.
        exists []. by repeat split => //.
      - unfold gen_init_mem_helper in Hgen. 
        fold gen_init_mem_helper in Hgen.
        move : Hgen => [len [Hchoose [lab [Hlab Hgen]]]]. 
        move: Hchoose => [/= /Z.compare_le_iff Hle1 /Z.compare_ge_iff Hle2].
        rewrite /C.min_frame_size /C.max_frame_size in Hle1 Hle2 *. 
        unfold alloc in Hgen.
        destruct (zreplicate_spec (Vint 0 @ ⊥) len) as [data [HIn [Heq HSome]]];
        try omega. rewrite HSome in Hgen. 
        remember (Mem.alloc Local mem ⊥ (Fr ⊥ lab data)) as alloc.
        destruct alloc as [fr mem'].    
        destruct (IHn mem') as [[lst [Hlen [Hforall Hfold]]] H] => //;  
        clear IHn.
        { rewrite /init_mem_spec in Hspec *.
          symmetry in Heqalloc. move : (Heqalloc) => Halloc.
          move => fr' lab' st' data' Hget. 
          apply Mem.alloc_get_frame with (b' := fr') in Halloc.
          destruct (equiv_dec fr fr'). 
          - inv e. rewrite Halloc in Hget. inv Hget. 
            rewrite /C.min_frame_size /C.max_frame_size Heq.
            repeat split => //; try (rewrite Z2Nat.id; omega).
            by apply gen_label_correct.
            by eapply Mem.alloc_stamp; apply Heqalloc.
          - apply Hspec. by rewrite -Halloc. } 
        split => //. exists ((lab, data) :: lst). split => //=; try by subst.
        split.  
        + move => lab' data'. move => [eq | HIn'].
          * inv eq.  
            rewrite Heq. repeat split; try (rewrite Z2Nat.id; omega).
            by apply gen_label_correct.
            assumption.
          * by apply Hforall.
        + by rewrite -Heqalloc. }
  { move => [[lst [Hlen [HIn Hfold]]] Hspec']. generalize dependent lst.
    generalize dependent m. 
    induction n as [| n IHn]; intros m Hspec lst Hlen HIn Hfold.
    - destruct lst; simpl in *. 
      rewrite returnGen_def. by auto. 
      congruence.
    - simpl. rewrite bindGen_def. 
      destruct lst as [|[lab data] lst]. simpl in Hlen; congruence.
      destruct (HIn lab data) as [[Hle1 Hle2] [HIn1 HIn2]]; try by apply in_eq.
      exists (Z.of_nat (length data)). split. 
      + rewrite choose_def. 
        split; by [apply Z.compare_le_iff | apply Z.compare_ge_iff]. 
      + exists lab. split; try by apply gen_label_correct.
        rewrite /alloc. 
        rewrite (zreplicate_eq data); auto; try omega; try by rewrite Nat2Z.id.
        remember (Mem.alloc Local m Zset.empty (Fr Zset.empty lab data)) as frm.
        destruct frm as [fr1 m1]. rewrite -Heqfrm. 
        apply IHn with (lst := lst). 
        * rewrite /init_mem_spec in Hspec *.
          move => block lab' st' data' Hget. 
          symmetry in Heqfrm. move: (Heqfrm)=> Halloc. 
          apply Mem.alloc_get_frame with (b' := block) in Halloc.
          destruct (equiv_dec fr1 block).
          - inv e.  rewrite Hget in Halloc. inv Halloc. 
            split => //. split => //. split => //. eapply Mem.alloc_stamp. 
            apply Heqfrm. 
          - rewrite Halloc in Hget. by apply Hspec.
       * by inversion Hlen.
       * move => lab' data' HIn'. 
         apply in_cons with (a := (lab, data)) in HIn'. by apply HIn in HIn'.
       * simpl in Hfold. by rewrite -Heqfrm in Hfold. }
Qed.
      


(* Lemma gen_init_mem_helper_soundness_old :  *)
(*   forall (top : Label) m lst n, *)
(*     init_mem_spec top m lst ->  *)
(*     pincl (gen_init_mem_helper top n (m, lst))  *)
(*          (fun pair' =>  *)
(*             ((length lst + n)%coq_nat = length (snd pair') /\ *)
(*              init_mem_spec top (fst pair') (snd pair'))). *)
(* Proof.  *)
(*   move => top m lst n [Hspec1 Hspec2] [m' lst']. *)
(*   { move => Hgen. generalize dependent lst.  generalize dependent m. *)
(*     generalize dependent m'. *)
(*     induction n as [| n IHn];  *)
(*     intros m' m lst Hspec1 Hspec2 Hgen. *)
(*     - rewrite /gen_init_mem_helper in Hgen. move: Hgen => [eq1 eq2]; subst. *)
(*       simpl. by split => //.  *)
(*     - simpl in *.  *)
(*       move: Hgen => [z [Hchoose [lab [/gen_label_correct Hlab Hgen]]]].  *)
(*       rewrite /alloc in Hgen. rewrite choose_def /C.min_frame_size in Hchoose. *)
(*       move: Hchoose => //= [/Z.compare_le_iff Hle1 /Z.compare_ge_iff Hle2]. *)
(*       destruct (zreplicate_spec (Vint 0 @ Zset.empty) z) as [data [H1 [H2 H3]]];  *)
(*       try omega. rewrite H3 in Hgen. *)
(*       remember (Mem.alloc Local m Zset.empty (Fr Zset.empty lab data)) as alloc. *)
(*       destruct alloc as [block m'']. rewrite -Heqalloc in Hgen.  *)
(*       have [Heq Hspec']:  *)
(*         ((length ((block, z) :: lst) + n)%coq_nat = length lst' /\  *)
(*          init_mem_spec top m' lst'). *)
(*       { apply : (IHn m' m'') => //.    *)
(*         - move => block' len HIn. destruct HIn  as [Heq | HIn].    *)
(*           + inv Heq. repeat split => //. *)
(*             * symmetry in Heqalloc. by apply Mem.alloc_stamp in Heqalloc. *)
(*             * exists lab. exists data. split => //.  *)
(*               symmetry in Heqalloc. by apply alloc_get_frame_new in Heqalloc. *)
(*               split => //. split => //. by move => v l /H1 [Heq1 Heq2]. *)
(*           + apply Hspec1 in HIn.  *)
(*             move : HIn => [H4 [H5 [lab' [data' [H6 [H7 [H8 H9]]]]]]].  *)
(*             repeat split => //. eexists. eexists. symmetry in Heqalloc. *)
(*             split => //. eapply alloc_get_frame_old; *)
(*             eassumption. by split => //. *)
(*         - move => [stamp lab' data'] b  Heq.  *)
(*           symmetry in Heqalloc. move : (Heqalloc) => Halloc. *)
(*           apply Mem.alloc_get_frame with (b' := b)in Heqalloc. *)
(*           destruct (equiv_dec block b).  *)
(*           + rewrite Heq in Heqalloc. inv Heqalloc; compute in e; subst.  *)
(*             split => //. split; [ by apply Mem.alloc_stamp in Halloc |].  *)
(*             split; [by rewrite H2 Z2Nat.id; try omega; apply in_eq |]. *)
(*             split => //; [ by move => v l /H1 [Heq1 Heq2] |].  *)
(*             rewrite H2 Z2Nat.id; try omega. by split => //. *)
(*           + rewrite Heqalloc in Heq. apply Hspec2 in Heq.  *)
(*             move : Heq => [H4 [H5 [H6 [H7 H8]]]].  *)
(*             repeat split => //. by apply in_cons. } *)
(*       split => //. by rewrite -Heq -plus_n_Sm /=. } *)
(* Qed.                                     *)
  
(* Instruction *)

Definition Instruction_spec (st : State) instr := 
  let '(St im m pr stk regs pc ) := st in
  let '(dptr, cptr, num, lab) :=
      groupRegisters st regs [] [] [] [] Z0 in
  match instr with 
    | Nop => True | Halt => False
    | PcLab z | PutBot z | Put _ z => (0 <= z <= (Zlength regs -1))%Z
    | Lab z1 z2 => 
      (0 <= z1 <= (Zlength regs-1))%Z /\ (0 <= z2 <= (Zlength regs-1))%Z
    | MLab z1 z2 | Load z1 z2 | Store z1 z2 | MSize z1 z2 | PGetOff z1 z2 => 
      dptr <> [] /\ In z1 dptr /\  (0 <= z2 <= (Zlength regs-1))%Z
    | FlowsTo z1 z2 z3 | LJoin z1 z2 z3 => 
      lab <> [] /\ In z1 lab /\ In z2 lab /\  (0 <= z3 <= (Zlength regs-1))%Z
    | BCall z1 z2 z3 => 
      cptr <> [] /\ lab <> [] /\  
      In z1 cptr /\ In z2 lab /\  (0 <= z3 <= (Zlength regs-1))%Z
    | BRet => (containsRet stk = true) 
    | Alloc z1 z2 z3 =>
      num <> [] /\ lab <> [] /\  
      In z1 num /\ In z2 lab /\  (0 <= z3 <= (Zlength regs-1))%Z
    | Jump z => cptr <> [] /\ In z cptr
    | BNZ z1 z2 => num <> [] /\ (-1 <= z1 <= 2)%Z /\ In z2 num
    | PSetOff z1 z2 z3 =>
      dptr <> [] /\ num <> [] /\  
      In z1 dptr /\ In z2 num /\  (0 <= z3 <= (Zlength regs-1))%Z
    | Output z1 => 
      num <> [] /\ In z1 num  
    | BinOp _ z1 z2 z3 => 
      num <> [] /\ In z1 num /\ In z2 num /\ (0 <= z3 <= (Zlength regs-1))%Z 
  end. 

Ltac discr_gen_eq :=
  match goal with 
    | H : (_, liftGen ?f ?gen) = (?n, ?g),
      Hg : ?g _ |- _ => 
        move : H => [Heq1 Heq2]; subst;
        rewrite liftGen_def in Hg; move: Hg => [a [_ H]]; discriminate
    | H : (_, returnGen ?a) = (?n, ?g),
      Hg : ?g _ |- _ => 
        move : H => [Heq1 Heq2]; subst; discriminate
    | H : (_, liftGen2 ?f ?gen1 ?gen2) = (?n, ?g),
      Hg : ?g _ |- _ => 
      move : H => [Heq1 Heq2]; subst;
      rewrite liftGen2_def in Hg;
      move: Hg => [a [_ [a' [_ H]]]]; subst; discriminate
    | H : (_, liftGen3 ?f ?gen1 ?gen2 ?gen3) = (?n, ?g),
      Hg : ?g _ |- _ =>
      move : H => [Heq1 Heq2]; subst;
      rewrite liftGen3_def in Hg;
      move: Hg => [a [_ [a' [_ [a'' [ _ H]]]]]]; subst; discriminate
    | H : (_, liftGen4 _ _ _ _ _) = (_, ?g),
      Hg : ?g _ |- _ =>
      move : H => [Heq1 Heq2]; subst;
      rewrite liftGen4_def in Hg;
      move: Hg => [a [_ [a' [_ [a'' [ _ [a''' [ _ H]]]]]]]]; subst; discriminate

  end.

Ltac discr_or_first := 
  match goal with 
    | HIn : ((_, _) = (_ , _) \/ _) |- _ =>  case: HIn => [Heq | HIn]; [discr_gen_eq | ]
    | HIn : In (_, _) _ |- _ => case: HIn => [Heq | HIn]; [discr_gen_eq | ]
  end.
 

Ltac unfold_gen := 
  match goal with
    | Hg : returnGen _ _ |- _ =>
      rewrite returnGen_def in Hg; subst
    | Hg : liftGen _ _ _ |- _ => 
      rewrite liftGen_def in Hg; move: Hg => [b [H1 [Heq]]]; subst
    | Hg : liftGen2 _ _ _ _ |- _ => 
      rewrite liftGen2_def in Hg; 
        move: Hg => [b [H1 [b' [H2 [Heq1 Heq2]]]]]; subst
    | Hg : liftGen3 _ _ _ _ _ |- _ => 
      rewrite liftGen3_def in Hg; 
        move: Hg => [b [H1 [b' [H2 [b'' [H3 [Heq1 Heq2 Heq3]]]]]]]; subst
    | Hg : liftGen4 _ _ _ _ _ _ |- _ => 
      rewrite liftGen4_def in Hg; 
       move: Hg=>[b [H1 [b' [H2 [b'' [ H3 [b''' [H4 [Heq1 Heq2 Heq3 Heq4]]]]]]]]]; subst
  end.


Ltac find_instr instr lst k :=
  match lst with
    | nil => k 0 (pure Nop) 
    | (?n, liftGen4 ?c ?a1 ?a2 ?a3 ?a4) :: ?lst' => (* match with liftGen4 *)
      match instr with
        | c _ _ _ _ => k n (liftGen4 c a1 a2 a3 a4)
        | _ => find_instr instr lst' k
      end 
    | (?n, liftGen3 ?c ?a1 ?a2 ?a3) :: ?lst' => (* match with liftGen3 *)
      match instr with
        | c _ _ _ => k n (liftGen3 c a1 a2 a3)
        | _ => find_instr instr lst' k
      end 
    | (?n, liftGen2 ?c ?a1 ?a2) :: ?lst' => (* match with liftGen2 *)
      match instr with
        | c _ _  => k n (liftGen2 c a1 a2)
        | _ => find_instr instr lst' k 
      end
    | (?n, liftGen ?c ?a1) :: ?lst' => (* match with liftGen *)
      match instr with
        | c _  => k n (liftGen c a1)
        | _ => find_instr instr lst' k
      end
    | (?n, ?f ?c) :: ?lst' => (* match with pure/returnGen *)
      match instr with
        | c  => k n (f c)
        | _ => find_instr instr lst' k
      end
  end. 


Ltac instantiate_exists :=
  match goal with 
    | |- exists n g, In (n, g) ?lst /\ _ ?cnstr /\ _ =>
      find_instr cnstr lst ltac:(fun n g => pose cnstr; exists n; exists g);
      split; [repeat ((try by apply in_eq); apply in_cons) | split => //]
  end.

Ltac try_solve2 := 
  match goal with 
    | Hand : _ /\ _ |- _ => destruct Hand; by try_solve2
    | |- _ = _ => reflexivity
    | |- _ /\ _ => split; [| by try_solve2]; by try_solve2
    | |- liftGen4 _ _ _ _ _ _ => rewrite liftGen4_def; by try_solve2
    | |- liftGen3 _ _ _ _ _ => rewrite liftGen3_def; by try_solve2
    | |- liftGen2 _ _ _ _ => rewrite liftGen2_def; by try_solve2
    | |- liftGen _ _ _ => rewrite liftGen_def; by try_solve2
    | |- elements _ _ _ => apply/elements_equiv; left; by try_solve2
    | |- choose _ _ => rewrite choose_def => /=; by try_solve2
    | |- ~ (_ ?= _)%Z = Lt => by apply/Z.compare_ge_iff
    | |- ~ (_ ?= _)%Z = Gt  => by apply/Z.compare_le_iff
    | |- ~ onNonEmpty ?l _ = 0 => by destruct l
    | |- exists _, _ => eexists; by try_solve2
    | |- ~ (( _ * onNonEmpty ?c _)%coq_nat * onNonEmpty ?l _)%coq_nat = 0 =>
        by destruct c; destruct l
    | |- gen_BinOpT _ => by apply gen_BinOpT_correct
    | |- ~ (if ?b then _ else _) = 0 => by destruct b
    | _ => by []
  end. 

Ltac try_solve :=
      match goal with 
        | |- _ /\ _ => split => //=; by try_solve
        | Hand : _ /\ _ |- _ => destruct Hand; by try_solve
        | Hor : _ \/ _ |- _ => destruct Hor; by try_solve
        | |- ~ _ => move => contra; subst; by try_solve
       | Hchoose : choose _ _ |- _ =>
          rewrite choose_def /= in Hchoose; by try_solve
        | Helem : elements _ _ _ |- _ => 
          move/elements_equiv : Helem => [Helem //= | [Helem1 Helem2] //=]; subst;
          by try_solve 
 
        | HIn: In _ [] |- _ => by []
        | Hnonempty : ~ (onNonEmpty [] _ = 0) |- _ =>
           by rewrite /onNonEmpty in Hnonempty
        | Hnonempty : ~ (_ * (onNonEmpty [] _))%coq_nat = 0 |- _ => 
            by rewrite [X in (_ * X)%coq_nat]/onNonEmpty -mult_n_O in Hnonempty
        | Hif: ~ ((if ?b then _ else _ ) = _) |- ?b = true =>
            by case: b Hif
        | |- (_ <= _)%Z => by apply/Z.compare_ge_iff
        | |- (_ <= _)%Z => by apply Z.compare_le_iff
        | |- _ => by []
      end. 

(* This is commented out as it takes a lot of time *)
(* Lemma gen_ainstrSSNI_correct : *)
(*   forall (st : State), (ainstrSSNI st) <--> (Instruction_spec st). *)
(* Proof. *)
(*   move=> st instr. rewrite /ainstrSSNI /Instruction_spec. *)
(*   case: st => im m pr stk regs pc. *)
(*   set st := {| *)
(*              st_imem := im; *)
(*              st_mem := m; *)
(*              st_pr := pr; *)
(*              st_stack := stk; *)
(*              st_regs := regs; *)
(*              st_pc := pc |}. *)
(*   case: (groupRegisters st regs [] [] [] [] Z0)=> [[[dptr cptr] num] lab]. *)
(*   split.   *)
(*   - case: instr => [r1 r2 | r1 r2 | r | r1 r2 r3 | | r1 r2 r3 | r1 r2 r3 | *)
(*                     r | | z r | bop r1 r2 r3 | r | z r | r1 r2 | r1 r2 | *)
(*                     r1 r2 r3 | r1 r2 r3 | r | | r1 r2 | r1 r2]; *)
(*     move /frequency_equiv =>  [[n [g [HIn [Hg Hn]]]] | [[H | H] H' //=]]; *)
(*     rewrite /gen_from_length /pure in HIn; repeat discr_or_first; *)
(*     by (case: HIn => [[Heq1 Heq2] | HIn]; subst;   *)
(*      [by unfold_gen; try_solve | by repeat discr_or_first]). *)
(*  -  Opaque mult choose. *)
(*     case: instr => [r1 r2 | r1 r2 | r | r1 r2 r3 | | r1 r2 r3 | r1 r2 r3 | *)
(*                     r | | z r | bop r1 r2 r3 | r | z r | r1 r2 | r1 r2 | *)
(*                     r1 r2 r3 | r1 r2 r3 | r | | r1 r2 | r1 r2]; *)
(*                    move => H; apply frequency_equiv; left;  *)
(*     instantiate_exists; try rewrite /gen_from_length; try by try_solve2. *)
(*     rewrite liftGen2_def. eexists. split; [| try_solve2]. *)
(*     rewrite /arbitrary /arbInt. by apply arbInt_correct. *)
(* Qed. *)



(* Proofs for variations *) 

(* Vary Atom *)
Lemma gen_vary_atom_correct :
  forall (l : Label) (a : Atom),
    let 'v @ la := a in 
    val_spec inf v -> 
    (gen_vary_atom l inf a) <--> (fun a' => 
                                    let 'v' @ la' := a' in 
                                    indist l a a' /\ val_spec inf v').
Proof.  
  move=> l a. case: a => va la.
  move=> Hspec; case => va' la'.
  rewrite /gen_vary_atom /indist /indistAtom /isHigh /isLow.  
  case: (la <: l). 
  + (* la lower that observability level *) 
    split.  
    * (* Correctness *)
      rewrite returnGen_def. move  => [Heq1 Heq2]; subst.  
      split => //. apply/andP; split. 
      by rewrite /label_eq; apply/andP; split; apply flows_refl. 
      apply/orP. right. rewrite /indist /indistValue /val_spec in Hspec *.   
      case: va' Hspec => [i' | Ptr' | i' | lv'] Hspec;
      repeat
      (match goal with 
        | |-  is_true (Z_eq ?n ?n) => 
          rewrite /Z_eq; by case (Z.eq_dec n n)
        | |- is_true (label_eq ?l ?l) => 
          rewrite /label_eq; apply/andP; split; apply flows_refl
        | |- _ => 
          case Ptr' => fp z; apply/andP; split; 
          [rewrite /mframe_eq; case: (Mem.EqDec_block fp fp) => //=; congruence |]
       end).   
    * (* Completeness *)
      move=> [/andP [/andP [Hflows1 Hflows2] /orP [H1 //= | H1]] H2]. 
      rewrite /indist /indistValue in H1. rewrite returnGen_def. 
      move: (flows_antisymm _ _ Hflows2 Hflows1) => Heq; subst.
      case: va Hspec H1 H2 => [i | ptr | i | lv];  
      case: va' => [i' | ptr' | i' | lv'] => // Hspec H1 H2; try 
       match goal with 
         | H : is_true (Z_eq ?i ?i') |- _ => 
           rewrite /Z_eq in H; by case : (Z.eq_dec i i') H => Heq H;  subst
         | H: is_true (match ?p with Ptr _ _ => false end) |- _ => by destruct p
         | H: is_true (label_eq ?l ?l') |- _ => 
           rewrite /label_eq in H; move/andP : H => [Hf1 Hf2]; 
           by move: (flows_antisymm _ _ Hf1 Hf2) => Heq; subst
       end. 
      case: ptr H1 {Hspec H2}; case : ptr' => fp z fp' z' /andP [H1 H2].
      rewrite /Z_eq in H2. rewrite /mframe_eq in H1.
      case: (Z.eq_dec z' z) H2 => //=; case: (Mem.EqDec_block fp' fp) H1 => //=.
      rewrite /equiv. by move => -> _ ->  _.
  + (* la higher than observable state *)
    rewrite bindGen_def. 
    split.    
    * (* Correctness *) 
      case: va Hspec=> [i | ptr | i | lv];  case: va' => [i' | ptr' | i' | lv'];
      move => Hpec [val [Hgen Hret]];
      rewrite returnGen_def in Hret; move : Hret => [Heq1 Heq2]; subst;
      (split; [apply/andP; split => //; rewrite /label_eq; apply/andP; split; 
                 by apply/flows_refl | 
               by apply gen_value_correct in Hgen]).
    * (* Completeness *) 
      move=> [/andP[/andP [H1 H2] /orP [_| H3]]   H];
      move: (flows_antisymm _ _ H2 H1) => Heq; subst;
      exists va'; split => //; by apply gen_value_correct.
Qed.
  
(* Vary Ptr_atom *)

Lemma gen_vary_pc_correct: 
  forall (obs: Label) (pc : Ptr_atom),
    (PC_spec pc) ->
    (gen_vary_pc obs inf pc) <--> (fun pc' =>
                                       indist obs pc pc' /\ PC_spec pc').
Proof.
  move => obs pc Hspec pc'.
  rewrite /gen_vary_pc /indist /indistPtrAtm /isHigh /isLow /pure. 
  case: pc Hspec => z lpc; case: pc' => z' lpc' Hspec.
  split. 
  + (* Correctness *)   
    remember (lpc <: obs) as b; 
    remember (lpc' <: obs) as b'.
    case: b Heqb; case: b' Heqb' => Heqb' Heqb.
    - move => [Heq Heq']; subst. split => //=.
      apply/andP. split. rewrite /label_eq. 
      by apply/andP; split; apply/flows_refl.
      rewrite /Z_eq. by case: (Z.eq_dec z' z').
    - move => [Heq Heq']; subst. congruence. 
    - rewrite bindGen_def. move => [pc'' [Hspec'' H]]. 
      case: pc'' Hspec'' H => z'' lpc''. 
      rewrite returnGen_def. move=> Hspec''. remember (lpc'' <: obs) as b''.
      case : b'' Heqb'' => Heqb'' ; move => [Heq1 Heq2]; subst; symmetry in Heqb. 
      * apply not_flows_not_join_flows_right with (l1 := lpc'') in Heqb.
        rewrite /join /ZsetLat -Heqb' in Heqb. congruence.
      * congruence.
    - rewrite bindGen_def. move => [pc'' [Hspec'' H]]. 
      case: pc'' Hspec'' H => z'' lpc'' /gen_PC_correct Hspec''.
      remember (lpc'' <: obs) as b''.
      case : b'' Heqb'' => Heqb''; move => [Heq1 Heq2]; subst;  
      symmetry in Heqb; split => //. 
      * rewrite /PC_spec -/Zset.union in Hspec'' Hspec *. 
        move : Hspec'' Hspec => [/allThingsBelow_isLow HIn'' Hrng] 
                                [/allThingsBelow_isLow HIn _].
        split => //=.
        apply/allThingsBelow_isLow'. (* This is admited ..*)
        by apply/join_minimal.
  + (* Completeness *)   
    Opaque PC_spec. remember (lpc <: obs) as b; 
    remember (lpc' <: obs) as b'.
    case: b Heqb; case: b' Heqb' => Heqb' Heqb [H1 H2] //.
    + move : H1 => /andP [/andP [Hf Hf'] H1']. rewrite /Z_eq in H1'.
      move: (flows_antisymm _ _ Hf Hf') => Heq; subst. 
      by case: ( Z.eq_dec z z') H1' => // Heq _; subst.
    + rewrite /PC_spec in H2. 
      rewrite bindGen_def. exists (PAtm z' lpc').
      split. by apply gen_PC_correct.
      by  rewrite -Heqb'. 
Qed.
  
(* Vary Stack *)

Fixpoint stack_size st : nat  := 
  match st with 
    | Mty => 0 
    | _ ::: st => S (stack_size st)
  end.

Lemma forallb2_forall : 
  forall (A : Type) (f : A -> A -> bool) (l1 l2 : list A),
    forallb2 f l1 l2 = true <-> 
    (length l1 = length l2 /\ 
     forall x y : A, In (x, y) (seq.zip l1 l2) -> f x y = true).
Proof.
  move=> A f l1 l2. split.
  + elim: l1 l2 => [| x l1 IHxs]; case => //= y l2 /andP [H1 H2].
    move/(_ l2 H2) : IHxs => [-> HIn]. split => //. 
    move=> x' y' [[Heq1 Heq2] | HIn']; subst; by auto.
  + elim: l1 l2 => [| x l1 IHxs]; case => [|y l2] //=; try by move => [H _].
    move => [Hlen HIn]. apply/andP; split. by eauto.
    apply IHxs. split; by eauto.
Qed.

Lemma zip_combine: 
  forall {A} {B} (l1 : list A) (l2 : list B), 
    length l1 = length l2 ->
    seq.zip l1 l2 = combine l1 l2.
Proof.
  move => A B. elim => //= [| x xs IHxs]; case => //= y yx Hlen.
  rewrite IHxs //. by apply/eq_add_S. 
Qed.
 

Lemma in_zip: 
  forall {A} {B} (l1 : list A) (l2 : list B) x y, 
  (In (x, y) (seq.zip l1 l2) -> (In x l1 /\ In y l2)).
Proof.
  Opaque In. 
  move => A B. elim => [| x xs IHxs]; case => // y ys x' y' [[Heq1 Heq2] | HIn]. 
  + by subst; split; apply in_eq. 
  + move/IHxs: HIn => [HIn1 HIn2]. split; constructor(assumption).
Qed.


Lemma in_map_zip : 
  forall {A B C} (l1 : list A) (l2 : list B) x y (f : B -> C), 
     In (x, y) (seq.zip l1 l2) -> In (x, f y) (seq.zip l1 (map f l2)).
Proof.
  move=> A B C. 
  elim => [| x xs IHxs]; case => // y ys x' y' f [[Heq1 Heq2] | HIn]; subst.
  + by constructor.
  + move/IHxs : HIn => /(_ f) HIn. 
    by constructor(assumption). 
Qed.

Lemma in_map_zip_iff : 
  forall {A B C} (l1 : list A) (l2 : list B) x y (f : B -> C), 
    In (x, y) (seq.zip l1 (map f l2)) <-> 
     exists z, f z = y /\ In (x, z) (seq.zip l1 l2).
Proof.
  move=> A B C. split. 
  - move: l1 l2 x y.
    elim => [| x xs IHxs]; case => // y ys x' y' [[Heq1 Heq2] | HIn]; subst.
    + exists y. split => //. by constructor.
    + move/IHxs : HIn => [z [Heq HIn]].  
      exists z. split => //. by constructor(assumption). 
  - move => [z' [Heq HIn]]. subst. by apply/in_map_zip.
Qed.


Lemma in_zip_swap:
    forall {A B} (l1 : list A) (l2 : list B) x y, 
     In (x, y) (seq.zip l1 l2) <->  In (y, x) (seq.zip l2 l1).
Proof.
  move=> A B. 
  elim => [| x xs IHxs]; case => // y ys x' y'. 
  split; move=>  [[Heq1 Heq2] | HIn] ; subst; (try by constructor);
  by move/IHxs: HIn => HIn; constructor(assumption).
Qed.

(* regSet *)
(* This function is used to smart_vary a regSet. I should edit the above proofs
   so they use this instead of reproving it every time *)

Lemma in_nth_iff: 
  forall {A} (l : list A) x,
    In x l <-> exists n, nth n l x = x /\ n < length l.
Proof.
  move=> A l x. split.
  - move=> HIn.  apply in_split in HIn. move : HIn => [l1 [l2 Heq]]. 
    exists (length l1). subst. split.
    + by rewrite app_nth2 // minus_diag. 
    + rewrite app_length. simpl. apply/ltP. 
      rewrite -[X in (_ + X)%coq_nat]addn1 [X in (X < _)%coq_nat]plus_n_O. 
      apply plus_lt_compat_l.  apply/leP. rewrite addn_gt0.  
      apply/orP; by right. 
  - move => [n [Heq Hle]]. rewrite -Heq. by apply/nth_In/leP. 
Qed.

Lemma nth_seqnth : 
  forall {A} (l : list A) n (x : A),
    seq.nth x l n = nth n l x.        
Proof.
  move=> A. elim. case =>//.  
  move=> a l H. move => n x. rewrite -seq.cat1s.
  rewrite seq.nth_cat. simpl. case: n => //= n. rewrite H.
  by rewrite -addn1 -[X in _ - X]add0n subnDr subn0. 
Qed.

Lemma nth_foralldef:
  forall {A} (l: list A) n (x x': A),
    n < length l -> nth n l x = nth n l x'.
Proof.
  move => A. elim=> // x xs IHxs n d d' Hlen. 
  case: n Hlen => //= n Hlen. auto.
Qed.

Lemma size_length:
  forall {A} (l :list A), seq.size l = length l. 
Proof.
  move=> A. elim => //.
Qed.

Lemma gen_vary_regSet_correct: 
  forall regs obs,
    (regs_spec inf regs)->
    (sequenceGen (map (@smart_vary _ _ (smart_vary_atom) obs inf) regs)) <-->
    (fun regs' => 
       regs_spec inf regs' /\ indist obs regs regs').
Proof.
  Opaque gen_vary_atom. 
  move => regs obs [Hlen Hspec] regs'. split.
  - (* Correctness *)
    move/sequenceGen_equiv=> [Hlen' HIn].
    rewrite /indist /indistReg. 
    split.    
    + (* regs_spec *)
      rewrite /regs_spec. split. 
      * by rewrite Hlen' map_length.
      * move=> [vr' lr'] HIn'. move: (HIn') => HIn''.
        apply in_split in HIn''. move : HIn'' => [l1 [l2 Heq]]. 
        case: regs Hlen Hspec Hlen' HIn. 
        - subst regs'. move=> _ _ Hlen' _. 
          rewrite app_length /= in Hlen'. omega. 
        - move => regsf regst. set regs := regsf :: regst.
          move=> Hlen Hspec Hlen' HIn. 
          remember (nth (length l1) regs regsf) as r1. 
          case: r1 Heqr1 => vr lr Heqr1.
          have/in_zip_swap Hzip : In (vr @ lr, vr' @ lr') (seq.zip regs regs').
          { apply in_nth_iff. exists (length l1). split.
            rewrite -nth_seqnth seq.nth_zip.         
            rewrite Heq !nth_seqnth app_nth2 // minus_diag.
            rewrite (nth_foralldef _ _ _ (vr @ lr)) in Heqr1.
            by rewrite -Heqr1. 
            rewrite map_length in Hlen'. rewrite -Hlen' Heq app_length.
            simpl. apply/ltP. 
            rewrite -[X in (_ + X)%coq_nat]addn1 [X in (X < _)%coq_nat]plus_n_O. 
            apply plus_lt_compat_l. apply/leP. rewrite addn_gt0.  
            apply/orP; by right. 
            rewrite !size_length. by rewrite map_length in Hlen'.
            rewrite -!size_length seq.size2_zip Heq seq.size_cat.
            rewrite -[X in X < _] addn0 ltn_add2l /= -[X in _ < X]addn1 addn_gt0. 
            by apply/orP; right. 
            rewrite map_length -!size_length in Hlen'.
            by rewrite -seq.size_cat -Hlen' Heq. }
          have /HIn Hind: In (vr' @ lr', (@smart_vary _ _ smart_vary_atom obs inf) (vr @ lr)) 
                 (seq.zip regs' (map (@smart_vary _ _ smart_vary_atom  obs inf) regs))
            by apply in_map_zip. 
          simpl in Hind. apply in_zip in Hzip. 
          move : Hzip => [HIn1 /Hspec [Hval HIn2]].
          move/(gen_vary_atom_correct _ (vr @ lr) Hval) : Hind => [Hind Hval']. 
          split => //. rewrite /indist /indistAtom in Hind. 
          move/andP: Hind => [/andP [Hle1 Hle2] _]. 
            by have -> : lr' = lr by apply/flows_antisymm. 
    + (* indist *)    
      apply forallb2_forall. split. 
      by rewrite map_length in Hlen'.
      move=> r r' /in_zip_swap Hzip. move: (Hzip) => HIn'.
      apply in_zip in HIn'. move: HIn' => [HIn1 HIn2]. 
      apply in_map_zip with (f := (@smart_vary _ _ smart_vary_atom obs inf)) 
        in Hzip. move/HIn : Hzip. simpl (snd _ _). 
      move: r r' HIn1 HIn2 => [vr lr] [vr' lr']  HIn1 /Hspec [Hval HIn2]. 
      by move/(gen_vary_atom_correct obs (vr @ lr) Hval) => [H _].
  - rewrite /regs_spec /indist /indistReg. 
    move => [[Hlen' Hreg] /forallb2_forall [Hlen'' Hind]]. apply/sequenceGen_equiv.
    split. by rewrite map_length. 
    move => [[vr' lr'] gen] /in_map_zip_iff  
            [[vr lr] [Heq  HIn]] /=; subst.
    move : (HIn) => /in_zip_swap/Hind Hind'.
    apply in_zip in HIn. move : HIn => [HIn1 HIn2].
    rewrite /smart_vary /smart_vary_atom. 
    move : (Hspec (vr @ lr) HIn2) => [Hval HIn].
    apply/ (gen_vary_atom_correct obs (vr @ lr) Hval).  split => //.
    by move : (Hreg (vr' @ lr') HIn1) => [Hval' _].
Qed.

Lemma gen_var_stack_sound_indist: 
  forall st obs pc,
    stack_spec pc inf st -> 
    pincl (gen_vary_stack obs inf st) (fun st' => 
                                   indist obs st st').
Proof.
  move=> st obs pc Hspec st'.
  rewrite /stack_spec in Hspec.
  move : Hspec => [Heq | [loc [Heq Hspec]]].
 (* Stack empty *)  
  - subst. by move => <-. 
 (* Stack Singleton *)   
  - subst. case: st'. 
    + rewrite /gen_vary_stack bindGen_def. move => [loc' [Hvary Hgen]].
      move: Hgen. rewrite bindGen_def. move=> [st' [_ Heq]]. discriminate.
    + rewrite /gen_vary_stack bindGen_def. move => loc' st' [loc'' [Hvary Hgen]].
      move: Hgen. rewrite bindGen_def /pure. move=> [st'' [Heq [Heq1 Heq2]]].
      rewrite returnGen_def in Heq. subst loc'' st'' st'. simpl.
      case: loc Hspec Hvary => [[[pc1 l] regs] regptr]. 
      case: loc' => [[[pc2 l'] regs'] regptr']. 
      rewrite /stack_loc_spec /smart_vary /smart_vary_stack_loc /gen_vary_stack_loc.
      case: pc1 => v_pc1 l_pc1; case: pc2 => v_pc2 l_pc2.
      remember  (isLow l_pc1 obs) as b.   
      case: b Heqb => Heqb [HIn [Hspec [Hrng1 [Hrng2 Hgen]]]]; rewrite -Heqb.
      - rewrite bindGen_def. 
        move => [regs'' [/sequenceGen_equiv [Hlen HIn'] [eq1 eq2 eq3 eq4 eq5]]]; 
        subst. rewrite -Heqb. rewrite /indistStackHelper.
        repeat (apply/andP; split => //; try rewrite /indist /indistPtrAtm -Heqb); 
        try (by rewrite /Z_eq; case: (Z.eq_dec _ _)); try by apply flows_refl.  
        apply forallb2_forall. split. by rewrite Hlen map_length. 
        move => r1 r2 HIn''. 
        have /HIn' H : In (r2, gen_vary_atom obs inf r1)
                             (seq.zip regs' (map (gen_vary_atom obs inf) regs))
        by apply/in_map_zip/in_zip_swap. 
        simpl in H. apply in_zip in HIn''. 
        move: Hspec HIn''=> [Hlen' Hval] [/Hval HIn1 HIn2].  
        case: r1 H HIn1 HIn2; case: r2 => v1 l1 v2 l H [Hvalspec HIn1] HIn2.
        by  move/(gen_vary_atom_correct obs (v2 @ l) Hvalspec): H => [H _].
      - rewrite bindGen_def. move => [regs'' [/vectorOf_equiv [Hlen Hvec] H]].
        move: H. move=> [eq1 eq2 eq3 eq4 eq5]; subst.
        by rewrite -Heqb.  
Qed.

Lemma gen_var_stack_sound_spec:
  forall st obs pc,
    stack_spec pc inf st -> 
    pincl (gen_vary_stack obs inf st) (fun st' => 
                                   stack_spec pc inf st' /\
                                   stack_size st = stack_size st').
Proof.
  move=> st obs pc Hspec st' Hvary.
  move : (gen_var_stack_sound_indist st obs pc Hspec st' Hvary) => Hindist.
  rewrite /stack_spec in Hspec.    
  move : Hspec => [Heq | [loc [Heq Hspec]]]. 
 (* Stack empty *)  
  - subst. move: Hvary. rewrite /gen_vary_stack /pure. 
    move => <-. split => //. by rewrite /stack_spec; left.
  - subst. move: Hvary . rewrite /gen_vary_stack /pure.  
    move=> [loc' [Hvary Hgen]]. move: Hgen.
    move => [st H]. rewrite !returnGen_def in H. move : H => [Heq1 Heq2]; subst.
    split => //. rewrite /stack_spec. right.
    exists loc'; split => //. rewrite /indist /indistStack in Hindist.
    case: loc Hspec Hvary Hindist => [[[pc1 l1] regs1] reg1]. 
    case: loc'=> [[[pc2 l2] regs2] reg2].
    rewrite /stack_loc_spec. case: pc1; case: pc2 => zpc1 lpc1 zpc2 lpc2.
    move => [HIn [Hregspec [Hrng1 [Hrng2 H]]]].
    remember (isLow lpc2 obs) as b.  case: b Heqb => Heqb. 
    + simpl.  rewrite -Heqb.   
      move=> [regs 
                [/(gen_vary_regSet_correct regs1 obs Hregspec) 
                  [Hregspec' Hindregs] [eq1 eq2 eq3 eq4]]] Heq Hind; 
      subst. by repeat split => //. 
    + rewrite /smart_vary /smart_vary_stack_loc /gen_vary_stack_loc 
              bindGen_def -Heqb.  
      move => [regs3 [/vectorOf_equiv [Hlen' HIn']] [eq1 eq2 eq3 eq4 eq5]] _; 
      subst. repeat split => //.   
      by move => r2 /HIn'/gen_atom_correct Hgen. 
Qed.

(* An additional specification that arises from the way we are generating stacks. *) 

Definition additional_stack_spec (st st' : Stack) obs : Prop:= 
  match st, st' with 
    | loc ::: Mty, loc' ::: Mty => 
      let '(pc, lab, regs, r) := loc in 
      let '(pc', lab', regs', r') := loc' in 
      (isLow ∂(pc) obs = true) \/ (pc = pc' /\ lab = lab' /\ r = r')
    | Mty, Mty => True
    | _, _ => False
  end.

Lemma gen_var_stack_sound_spec_add:
  forall st obs pc,
    stack_spec pc inf st -> 
    pincl (gen_vary_stack obs inf st) (fun st' => 
                                         additional_stack_spec st st' obs).
Proof.
  move => st obs pc Hspec st'.
  case: st Hspec => // [| loc st].
  + (* Stack Empty *)
    rewrite /stack_spec /gen_vary_stack /pure returnGen_def.
    by move => _ <-.
  + (* Stack singleton *)
    rewrite /stack_spec /gen_vary_stack /pure.
    move => [//= | [loc' [[Heq1 Heq2] Hspec]]]; subst loc' st.
    move => [loc' [Hvary [st'' [Hret1 Hret2]]]].
    rewrite !returnGen_def in Hret1 Hret2. subst.
    case: loc {Hspec} Hvary => [[[ret_pc lab] regs] r].
    case: loc'  => [[[ret_pc' lab'] regs'] r']. 
    simpl. case: (isLow ∂(ret_pc) obs) => [_ | [rs [Hrs [eq1 eq2 eq3 eq4]]]].
    by left.
    by right; subst.
Qed.

Lemma gen_var_stack_complete: 
  forall st obs pc,
    stack_spec pc inf st -> 
    pincl (fun st' => 
             indist obs st st' /\
             stack_spec pc inf st' /\
             stack_size st = stack_size st' /\
             additional_stack_spec st st' obs
          )
  (gen_vary_stack obs inf st).
Proof.
  move=> st obs pc Hspec st'. 
  case: st Hspec.
  + (* Stack empty *)
    simpl. case: st' => //. by  move => loc st _ [_ [ _ [_ H]]].
  + (* Stack singleton *)
    case: st'.
    - rewrite /additional_stack_spec.
      by move => loc; case => [| loc' st'] _ [_ [_ [_ H ]]].  
    - rewrite /stack_spec /stack_loc_spec /additional_stack_spec. 
      move => [[[ret_pc' lab'] regs'] r'] st' [[[ret_pc lab] regs] r] st. 
      move => [// | [loc [[eq1 eq2] Hspec]]]
              [Hind [[//| [loc' [[eq1' eq2'] Hspec']]]]]
              [_ Hadd]; subst. rewrite /gen_vary_stack.
      rewrite bindGen_def /smart_vary /smart_vary_stack_loc /gen_vary_stack_loc.
      rewrite /indist /indistStack /cropTop in Hind.   
      remember (isLow ∂(ret_pc) obs) as b. 
      case: b Heqb Hadd Hind => Heqb Hadd Hind /=. 
      * remember (isLow ∂(ret_pc') obs) as b'. 
        case: b' Heqb' Hind => Heqb'  Hind; 
        rewrite /indistStackHelper in Hind => //. 
        move/andP : Hind => [/andP [/andP [/andP [Heq1 Hind2] Heq3] Hind] _].
        rewrite /Z_eq in Heq3. case: (Z.eq_dec r r') Heq3 => // eq _; subst.
        rewrite /label_eq in Heq1. move/andP : Heq1 => [H1 H2].
        have eq : lab = lab' by apply flows_antisymm. subst. 
        rewrite bindGen_def. clear Hadd H1 H2. eexists. split => //.
        exists regs'. split=> //. 
        move: Hspec Hspec' => [_ [Hregs _]] [_ [Hregs' _]].
        by apply/(gen_vary_regSet_correct regs obs Hregs).
        rewrite bindGen_def. eexists; split => //.
        rewrite /indist /indistPtrAtm in Hind2.
        case: ret_pc Heqb Hind2 {Hspec} => pc_i pc_l Heqb Hind2.
        case: ret_pc' Heqb' Hind2 {Hspec'}  => pc_i' pc_l' Heqb' Hind2.
        rewrite -Heqb -Heqb' /= in Hind2. move/andP: Hind2 => [Heq1 Heq2].
        rewrite /Z_eq in Heq2. case: (Z.eq_dec pc_i pc_i') Heq2 => // eq _; subst.
        rewrite /label_eq in Heq1. move/andP : Heq1 => [H1 H2].
        have eq : pc_l = pc_l' by apply flows_antisymm. by subst.
      * move : Hadd => [// | [eq1 [eq2 eq3]]]; subst.
        rewrite -Heqb in Hind. eexists. split; [| eexists; split => //].
        eexists. split=> //. apply vectorOf_equiv. 
        move : Hspec' => [_ [[Hlen Hregs] _]]. split => //.
        move=> r /Hregs HInd. by apply gen_atom_correct. 
Qed.

Lemma gen_var_stack_correct: 
  forall st obs pc,
    stack_spec pc inf st -> 
    (gen_vary_stack obs inf st) <-->
    (fun st' => 
       indist obs st st' /\
       additional_stack_spec st st' obs /\
       stack_spec pc inf st' /\
       stack_size st = stack_size st').
Proof.
  move=> st obs pc Hspec st'. split.
  move=> H. split; [| split].
  * + by apply/gen_var_stack_sound_indist.
    + by apply/gen_var_stack_sound_spec_add.
    + by apply/gen_var_stack_sound_spec. 
  * move => [H1 [H2 [H3 H4]]]. by apply/gen_var_stack_complete.
Qed.



(* Old indist proof for alternative generator *)
(* Lemma gen_var_stack_sound_indist:  *)
(*   forall st obs pc, *)
(*     stack_spec pc inf st ->  *)
(*     pincl (gen_vary_stack obs inf st) (fun st' =>  *)
(*                                    indist obs st st'). *)
(* Proof. *)
(*   move=> st obs pc Hspec st'. *)
(*   rewrite /stack_spec in Hspec. *)
(*   move : Hspec => [Heq | [loc [Heq Hspec]]]. *)
(*  (* Stack empty *)   *)
(*   - subst. by move => <-.  *)
(*  (* Stack Singleton *)    *)
(*   - subst. case: st'.  *)
(*     + rewrite /gen_vary_stack bindGen_def. move => [loc' [Hvary Hgen]]. *)
(*       move: Hgen. rewrite bindGen_def. move=> [st' [_ Heq]]. discriminate. *)
(*     + rewrite /gen_vary_stack bindGen_def. move => loc' st' [loc'' [Hvary Hgen]]. *)
(*       move: Hgen. rewrite bindGen_def /pure. move=> [st'' [Heq [Heq1 Heq2]]]. *)
(*       rewrite returnGen_def in Heq. subst loc'' st'' st'. simpl. *)
(*       case: loc Hspec Hvary => [[[pc1 l] regs] regptr].  *)
(*       case: loc' => [[[pc2 l'] regs'] regptr'].  *)
(*       rewrite /stack_loc_spec /smart_vary /smart_vary_stack_loc /gen_vary_stack_loc. *)
(*       case: pc1 => v_pc1 l_pc1; case: pc2 => v_pc2 l_pc2. *)
(*       remember  (isLow l_pc1 obs) as b.    *)
(*       case: b Heqb => Heqb [HIn [Hspec [Hrng1 [Hrng2 Hgen]]]]; rewrite -Heqb. *)
(*       - rewrite bindGen_def.  *)
(*         move => [regs'' [/sequenceGen_equiv [Hlen HIn'] [eq1 eq2 eq3 eq4 eq5]]];  *)
(*         subst. rewrite -Heqb. rewrite /indistStackHelper. *)
(*         repeat (apply/andP; split => //; try rewrite /indist /indistPtrAtm -Heqb);  *)
(*         try (by rewrite /Z_eq; case: (Z.eq_dec _ _)); try by apply flows_refl.   *)
(*         apply forallb2_forall. split. by rewrite Hlen map_length.  *)
(*         move => r1 r2 HIn''.  *)
(*         have /HIn' H : In (r2, gen_vary_atom obs inf r1) *)
(*                              (seq.zip regs' (map (gen_vary_atom obs inf) regs)) *)
(*         by apply/in_map_zip/in_zip_swap.  *)
(*         simpl in H. apply in_zip in HIn''.  *)
(*         move: Hspec HIn''=> [Hlen' Hval] [/Hval HIn1 HIn2].   *)
(*         case: r1 H HIn1 HIn2; case: r2 => v1 l1 v2 l H [Hvalspec HIn1] HIn2. *)
(*         by  move/(gen_vary_atom_correct obs (v2 @ l) Hvalspec): H => [H _]. *)
(*       - rewrite bindGen_def. move => [regs'' [/vectorOf_equiv [Hlen Hvec] H]]. *)
(*         move: H. rewrite bindGen_def. move=> [regps'' [Hvary H]]. *)
(*          move: H. rewrite bindGen_def. move=> [lab'' [Hgenlab H]]. *)
(*          move: H. rewrite bindGen_def. move=> [regptr'' [Hgenreg [Heq1 Heq2 Heq3 Heq4]]]. *)
(*          subst. rewrite /smart_vary /smart_vary_pc /gen_vary_pc in Hgen Hvary. *)
(*          rewrite -Heqb bindGen_def in Hvary. move: Hvary => [pc3 [H1 H2]]. *)
(*          case: pc3 H1 H2=> v_pc3 l_pc3 H1 H2. rewrite /isHigh in H2.  *)
(*          remember (isLow l_pc3 obs) as b'.   *)
(*          case: b' Heqb' H2 =>  Heqb' /= [Heq1 Heq2]; subst.  *)
(*          - symmetry in Heqb. simpl in Heqb.  *)
(*            move: (not_flows_not_join_flows_right obs l_pc3 l_pc1 Heqb). *)
(*            rewrite /join /ZsetLat /isLow. move => -> . split => //. *)
(*          - rewrite -Heqb'. split => //.  *)
(* Qed. *)
      

   


Axiom frame_spec' : Info -> frame -> Prop.    

Lemma gen_var_frame_correct:
  forall (obs: Label) (inf: Info) (fr : frame),
    (frame_spec' inf fr) -> 
    (gen_var_frame obs inf fr) <--> (fun fr' => 
                                        indist obs fr fr' /\ frame_spec' inf fr').
Proof. admit. Qed.

Axiom mem_spec : Info -> memory -> Prop.    

Lemma gen_vary_memory_correct:
  forall (obs: Label) (inf: Info) (m : memory),
    (mem_spec inf m) -> 
    (gen_vary_memory obs inf m) <--> (fun m' => 
                                        indist obs m m' /\ mem_spec inf m').
Proof. admit. Qed.





(* Main theorem *)

Lemma combine_l : forall {A} (l : list A) x y, 
                    In (x, y) (combine l l) -> x = y.
Proof. admit. Qed.

Lemma incl_empty : forall s, Zset.incl Zset.empty s.
Proof.
  move=> s. apply Zset.incl_spec. by rewrite Zset.elements_empty. 
Qed.

Lemma incl_same : forall s, Zset.incl s s.
Proof.
  move => s.
  by apply/Zset.incl_spec/incl_refl. 
Qed.

Require Import ZArith.

Lemma forallb_indist : 
  forall (l : list frame),
    forallb
      (fun x : frame * frame =>
         let (f1, f2) := x in indist Zset.empty f1 f2)
      (combine l l).
Proof.
  move => l. apply forallb_forall. case => x y H.
  apply combine_l in H. subst. case: y => s lab l0. 
  rewrite /indist /indistFrame /isLow.
  case: (s <: Zset.empty) =>  //=.  
  rewrite /label_eq flows_refl /=.
  case: (Zset.incl lab Zset.empty) =>  //=. 
  elim : l0 => // x l0 IHl0. simpl.
  apply/andP. split => //=.
Abort.
(*
  case: x => valx labx. rewrite incl_same //=. 
  rewrite /isHigh /isLow .  
  case: (labx <: Zset.empty)=> //= .
  case: valx => //=. 
  try (by rewrite /Z_eq; move => n ; case (Z.eq_dec n n)).
  case. move => fp i. apply/andP. split => //. 
  rewrite /mframe_eq. 
  case: (Mem.EqDec_block fp fp) => //=. 
  congruence. by rewrite /Z_eq; case: (Z.eq_dec i i).
  (by rewrite /Z_eq; move => n ; case (Z.eq_dec n n)).
  move => L; apply/andP; split; apply incl_same.
Qed.
*)

Lemma gen_variation_state_correct :
  gen_variation_state <--> (fun b =>
                              let '(Var L s1 s2) := b in
                              indist L s1 s2 = true).
Proof.
  (* The statement is not complete as we need the states to satisfy 
     some validity requirements *)
Abort.
  (* case => Lab s1 s2. split. rewrite /gen_variation_state.  *)
  (* rewrite bindGen_def.  *)
  (* move => [l1 [Htop H]].  *)
  (* rewrite bindGen_def in H.  *)
  (* move: H => [[mem mframes] [Hinit H]].  *)
  (* case: mframes Hinit H => [ | mframe1 mframes] Hinit H. *)
  (* - rewrite returnGen_def /= in H.  *)
  (*   move : H => [Heq1 Heq2 Heq3]. subst.  *)
  (*   rewrite /indist /indistState /failed_state !trace_axiom //=. *)
  (*   rewrite /label_eq /isHigh /isLow /flows. simpl.  *)
  (*   have Ht: Zset.incl Zset.empty Zset.empty = true by *)
  (*       apply/Zset.incl_spec; rewrite Zset.elements_empty.  *)
  (*   rewrite Ht -beq_nat_refl /indistMemHelper.  *)
  (*   simpl. by rewrite forallb_indist. *)
  (* - case : mframe1 Hinit H => mf1 Z1 Hinit H1. *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [ptr_a [sgen H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [regset [sgen2 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [st [sgen3 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [memg [sgen4 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [instr [sgen5 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [lab [sgen6 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [ST' [sgen7 H1]].      *)
  (*   rewrite returnGen_def in H1. *)
  (*   move : H1 => [Heq1 Heq2 Heq3]; subst. *)
  (*   rewrite /smart_gen in sgen, sgen2, sgen3, sgen4, sgen5, sgen6, sgen7 . *)

Abort All.
End WithDataLenNonEmpty.
