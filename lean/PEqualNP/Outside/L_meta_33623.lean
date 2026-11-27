import Mathlib.Data.Matrix.ColumnRowPartitioned
import PEqualNP.Outside.L_meta_25647

namespace PEqualNP.Outside.L_meta_33623_aux
open Matrix
open PEqualNP.Outside.L_meta_25647_aux
abbrev F := ZMod 2
abbrev Mat (i j : Nat) := Matrix (Fin i) (Fin j) F
abbrev Sq (r : Nat) := Mat r r

def bit (b : Bool) : F := (b.toNat : F)
theorem bit_eq (b : Bool) : bit b=b2z b := by cases b <;> rfl
theorem bit_dec (x : F) : bit (decide (x=1))=x := by revert x;decide
theorem xor_bit (a b : Bool) : bit (xor a b)=bit a-bit b := by cases a <;> cases b <;> decide
theorem two (a : F) : a+a=0 := by revert a;decide

theorem addRank (A B : Mat m n) : (A+B).rank≤A.rank+B.rank := by
  have h := LinearMap.rank_add_le A.mulVecLin B.mulVecLin
  simp only [LinearMap.rank, ← Submodule.finrank_eq_rank, ← Nat.cast_add] at h
  change Module.finrank F (LinearMap.range (A+B).mulVecLin)≤_
  rw [Matrix.mulVecLin_add]
  exact_mod_cast h

theorem dist (A B C : Mat m n) : (A-C).rank≤(A-B).rank+(B-C).rank := by
  simpa only [sub_add_sub_cancel] using addRank (A-B) (B-C)

theorem factor (A : Mat m n) (h : A.rank≤w) : ∃ U : Mat m w, ∃ V : Mat w n, U*V=A := by
  obtain ⟨u,v,eq⟩ := factor_of_rank_le A h
  exact ⟨fun i k => u k i,v,by ext i j;exact (eq i j).symm⟩

/-- The diagonal and successor products are identities after changing bases on each panel. -/
def Frames (k r w : Nat) (H : Sq r) :=
  ∃ (A : Fin (k+2) → Mat r w) (B : Fin (k+2) → Mat w r),
    (∀ i, A i * B i=1) ∧ (∀ j : Fin (k+1), A j.castSucc * B j.succ=1) ∧
    A (Fin.last (k+1)) * B 0=H

theorem necessary {H : Sq r} (h : Frames k r w H) :
    r≤w ∧ r≤H.rank+(w-r) ∧ (1-H).rank≤(k+1)*(w-r) := by
  obtain ⟨A,B,diag,next,last⟩ := h
  have leA (i) : r≤(A i).rank := by simpa [diag] using rank_mul_le_left (A i) (B i)
  have leB (i) : r≤(B i).rank := by simpa [diag] using rank_mul_le_right (A i) (B i)
  have rw' : r≤w := (leA 0).trans (by simpa using rank_le_card_width (A 0))
  have close := rank_mul_ge (A (Fin.last (k+1))) (B 0)
  rw [last,Fintype.card_fin] at close
  have lo := leA (Fin.last (k+1))
  have ro := leB 0
  refine ⟨rw',by omega,?_⟩
  let S := fun i => A i * B 0
  have step (j : Fin (k+1)) : (S j.castSucc-S j.succ).rank≤w-r := by
    have z : (A j.castSucc-A j.succ)*B j.succ=0 := by rw [Matrix.sub_mul,next,diag,sub_self]
    have d := rank_add_rank_le_card_of_mul_eq_zero z
    rw [Fintype.card_fin] at d
    have b := leB j.succ
    have v := rank_mul_le_left (A j.castSucc-A j.succ) (B 0)
    rw [Matrix.sub_mul] at v
    exact v.trans (by omega)
  have run (i : Fin (k+2)) : (S 0-S i).rank≤ i.val*(w-r) := by
    induction i using Fin.induction with
    | zero => simp
    | succ j ih =>
      have d := dist (S 0) (S j.castSucc) (S j.succ)
      have s := step j
      simpa [Fin.val_succ,Nat.succ_mul] using d.trans (Nat.add_le_add ih s)
  have h := run (Fin.last (k+1))
  simpa [S,diag,last] using h

def Anchor (P : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) : Mat n m :=
  fun a b => bit (P a b)+bit (P u b)+bit (P a v)+bit (P u v)

theorem criterion (P : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t) :
    (Anchor P u v).rank≤2*t ↔ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    ((∀ g∈C.gates,g.inputs.length≤2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    PEqualNP.Represents.Represents P C) ∧
    (depthsOf (n+m) C.gates).getD C.output 0≤1 ∧ C.gates.countP nlGate≤t := by
  have same : Anchor P u v=anchor u v (fun i j => b2z (P i j)) := by
    ext;unfold Anchor anchor;simp only [bit_eq];abel
  rw [same]
  exact main n m P u v t

def Rects (e : Nat) (D : Sq r) := ∃ X Y : Fin e → Finset (Fin r), ∀ a b,
  D a b=bit (decide ((Finset.univ.filter (fun j : Fin e => a ∈ X j ∧ b ∈ Y j)).card % 2=1))

theorem parity (s : Finset α) (p : α → Prop) [DecidablePred p] :
    bit (decide ((s.filter p).card%2=1)) = ∑ k∈s, (if p k then 1 else 0 : F) := by
  rw [Finset.sum_boole]
  generalize (s.filter p).card=l
  have e : (l : F)=(l%2 : Nat) := (ZMod.natCast_mod l 2).symm
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one l with h|h <;> simp [h,bit]

theorem rect_iff (D : Sq r) : Rects e D ↔ D.rank≤e := by
  classical
  constructor
  · rintro ⟨X,Y,eq⟩
    let U : Mat r e := fun a j => if a∈X j then 1 else 0
    let V : Mat e r := fun j b => if b∈Y j then 1 else 0
    have f : D=U*V := by
      ext a b;rw [eq,parity,Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _;by_cases h : a∈X j <;> by_cases h' : b∈Y j <;> simp [U,V,h,h']
    rw [f];exact rank_of_factor _ _
  · intro h
    obtain ⟨U,V,eq⟩ := factor D h
    refine ⟨fun j => Finset.univ.filter (fun a => U a j=1),
            fun j => Finset.univ.filter (fun b => V j b=1),?_⟩
    intro a b
    rw [←eq,Matrix.mul_apply,parity]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    generalize U a j=x;generalize V j b=y;revert x y;decide
end PEqualNP.Outside.L_meta_33623_aux

namespace PEqualNP.Outside.L_meta_33623_aux
open Matrix
open PEqualNP.Outside.L_meta_25647_aux

abbrev Idx (k : Nat) := Fin (k+2)
abbrev Panel (k r n : Nat) := Idx k × Fin r ↪ Fin n

def block (rows : Panel k r n) (cols : Panel k r m) (u : Fin n) (v : Fin m)
    (P : Fin n → Fin m → Bool) (i j : Idx k) : Sq r :=
  fun a b => Anchor P u v (rows (i,a)) (cols (j,b))

def errs (rows : Panel k r n) (cols : Panel k r m)
    (P T : Fin n → Fin m → Bool) (e : Nat) :=
  ∃ X Y : Fin e → Finset (Fin r), ∀ a b,
    xor (P (rows (Fin.last (k+1),a)) (cols (0,b))) (T (rows (Fin.last (k+1),a)) (cols (0,b))) =
      decide ((Finset.univ.filter (fun j : Fin e => a∈X j ∧ b∈Y j)).card%2=1)

theorem errRank (rows : Panel k r n) (cols : Panel k r m) (u : Fin n) (v : Fin m)
    (P T : Fin n → Fin m → Bool) (col : ∀ a,P a v=T a v) (row : ∀ b,P u b=T u b) :
    errs rows cols P T e ↔ (block rows cols u v P (Fin.last _) 0-block rows cols u v T (Fin.last _) 0).rank≤e := by
  rw [←rect_iff]
  have bitInj : Function.Injective bit := by intro a b h;apply b2z_inj;simpa only [←bit_eq] using h
  have delta (a b) : (block rows cols u v P (Fin.last _) 0-block rows cols u v T (Fin.last _) 0) a b =
      bit (xor (P (rows (Fin.last _,a)) (cols (0,b))) (T (rows (Fin.last _,a)) (cols (0,b)))) := by
    simp only [Matrix.sub_apply,block,Anchor,col,row,xor_bit]
    abel
  constructor
  · rintro ⟨X,Y,h⟩;exact ⟨X,Y,fun a b => (delta a b).trans (congrArg bit (h a b))⟩
  · rintro ⟨X,Y,h⟩;exact ⟨X,Y,fun a b => bitInj ((delta a b).symm.trans (h a b))⟩

theorem extendPanel (rows : Panel k r n) (cols : Panel k r m) (u : Fin n) (v : Fin m)
    (ru : ∀ z,rows z≠u) (cv : ∀ z,cols z≠v) (T : Fin n → Fin m → Bool)
    (U : Idx k → Mat r w) (V : Idx k → Mat w r) :
    ∃ P, (∀ a,P a v=T a v) ∧ (∀ b,P u b=T u b) ∧
      (Anchor P u v).rank≤w ∧ ∀ i j,block rows cols u v P i j=U i*V j := by
  classical
  let A : Mat n w := Function.extend rows (fun z => U z.1 z.2) (fun _ => 0)
  let ys := Function.extend cols (fun z h => V z.1 h z.2) (fun _ _ => (0:F))
  let B : Mat w m := fun h b => ys b h
  have au : A u=0 := Function.extend_apply' _ _ _ (by simpa using ru)
  have bv (i) : B i v=0 := by
    have h : ys v=fun _ => 0 := Function.extend_apply' _ _ _ (by simpa using cv)
    exact congrFun h i
  let M := A*B
  have mu (j) : M u j=0 := by simp [M,Matrix.mul_apply,au]
  have mv (i) : M i v=0 := by simp [M,Matrix.mul_apply,bv]
  let P := fun a b => decide (M a b+bit (T a v)+bit (T u b)+bit (T u v)=1)
  have col (a) : P a v=T a v := by
    simp only [P,mv,zero_add,add_assoc,two,add_zero]
    cases T a v <;> decide
  have row (b) : P u b=T u b := by
    simp only [P,mu,zero_add,add_right_comm (bit (T u v)),two,zero_add]
    cases T u b <;> decide
  have eq : Anchor P u v=M := by
    ext a b
    simp only [Anchor,row,col,P,bit_dec]
    generalize bit (T u v)=x;generalize bit (T a v)=y;generalize bit (T u b)=z
    have := two x;have := two y;have := two z;linear_combination ‹x+x=0›+‹y+y=0›+‹z+z=0›
  refine ⟨P,col,row,eq ▸ rank_of_factor A B,?_⟩
  intro i j;ext a b
  change Anchor P u v _ _=_
  rw [eq]
  change (A*B) (rows (i,a)) (cols (j,b))=(U i*V j) a b
  rw [Matrix.mul_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro h _
  simp only [A,B,ys,rows.injective.extend_apply,cols.injective.extend_apply]

def PanelRank (rows : Panel k r n) (cols : Panel k r m) (u : Fin n) (v : Fin m)
    (T : Fin n → Fin m → Bool) (w e : Nat) :=
  ∃ P, (Anchor P u v).rank≤w ∧ (∀ a,P a v=T a v) ∧ (∀ b,P u b=T u b) ∧
    (∀ i,block rows cols u v P i i=block rows cols u v T i i) ∧
    (∀ j : Fin (k+1),block rows cols u v P j.castSucc j.succ=block rows cols u v T j.castSucc j.succ) ∧
    errs rows cols P T e

/-- Restrict the anchored matrix to the panels, or extend panel factors by zero at unused labels. -/
theorem panel_iff (rows : Panel k r n) (cols : Panel k r m) (u : Fin n) (v : Fin m)
    (ru : ∀ z,rows z≠u) (cv : ∀ z,cols z≠v) (T : Fin n → Fin m → Bool)
    (L R : Idx k → Sq r) (H : Sq r) (units : ∀ i,IsUnit (L i) ∧ IsUnit (R i))
    (diag : ∀ i,block rows cols u v T i i=L i*R i)
    (next : ∀ j : Fin (k+1),block rows cols u v T j.castSucc j.succ=L j.castSucc*R j.succ)
    (last : block rows cols u v T (Fin.last _) 0=L (Fin.last _)*H*R 0) :
    PanelRank rows cols u v T w e ↔ ∃ S : Sq r, Frames k r w S ∧ (S-H).rank≤e := by
  classical
  let l := Fin.last (k+1)
  have lu (i) := (L i).isUnit_iff_isUnit_det.mp (units i).1
  have rv (i) := (R i).isUnit_iff_isUnit_det.mp (units i).2
  have sameRank (D : Sq r) : (L l*D*R 0).rank=D.rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (rv 0), Matrix.rank_mul_eq_right_of_isUnit_det _ _ (lu l)]
  constructor
  · rintro ⟨P,pr,pc,pq,pd,pn,pe⟩
    obtain ⟨U,V,fac⟩ := factor _ pr
    let X : Idx k → Mat r w := fun i a h => U (rows (i,a)) h
    let Y : Idx k → Mat w r := fun i h b => V h (cols (i,b))
    have eq (i j) : X i*Y j=block rows cols u v P i j := by
      ext a b;exact congrFun (congrFun fac (rows (i,a))) (cols (j,b))
    let A : Idx k → Mat r w := fun i => (L i)⁻¹*X i
    let B : Idx k → Mat w r := fun j => Y j*(R j)⁻¹
    have scale (i j) : A i*B j=(L i)⁻¹*(block rows cols u v P i j)*(R j)⁻¹ := by
      rw [←eq];simp only [A,B,Matrix.mul_assoc]
    have norm (i j) (h : block rows cols u v P i j=L i*R j) : A i*B j=1 := by
      rw [scale,h,←Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (lu i),one_mul,Matrix.mul_nonsing_inv _ (rv j)]
    refine ⟨A l*B 0,⟨A,B,fun i => norm i i ((pd i).trans (diag i)),
      fun j => norm _ _ ((pn j).trans (next j)),rfl⟩,?_⟩
    have close := (errRank rows cols u v P T pc pq).mp pe
    have cancel : L l*(A l*B 0)*R 0=block rows cols u v P l 0 := by
      rw [scale];simp only [Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (rv 0),mul_one]
      rw [←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (lu l),one_mul]
    rw [←sameRank, Matrix.mul_sub,Matrix.sub_mul,cancel,←last];exact close
  · rintro ⟨S,⟨A,B,ad,an,al⟩,err⟩
    obtain ⟨P,pc,pq,pr,h⟩ := extendPanel rows cols u v ru cv T (fun i => L i*A i) (fun j => B j*R j)
    have eq (i j) : block rows cols u v P i j=L i*(A i*B j)*R j := by rw [h];simp [Matrix.mul_assoc]
    refine ⟨P,pr,pc,pq,fun i => by rw [eq,ad,mul_one,diag],fun j => by rw [eq,an,mul_one,next],?_⟩
    apply (errRank rows cols u v P T pc pq).mpr
    rw [eq,al,last,←Matrix.sub_mul,←Matrix.mul_sub]
    exact (sameRank _).le.trans err
end PEqualNP.Outside.L_meta_33623_aux

namespace PEqualNP.Outside.L_meta_33623_aux
open LinearMap Submodule Module Matrix
abbrev Vect (r : Nat) := Fin r → F
abbrev Endo (r : Nat) := Vect r →ₗ[F] Vect r

private theorem outsideBoth (U W : Submodule F (Vect r)) (u : U≠⊤) (w : W≠⊤) :
    ∃ x, x∉U ∧ x∉W := by
  obtain ⟨a,_,ha⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr u)
  obtain ⟨b,_,hb⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr w)
  by_cases aw : a∈W
  · by_cases bu : b∈U
    · exact ⟨a+b,fun h => ha ((U.add_mem_iff_left bu).mp h),fun h => hb ((W.add_mem_iff_right aw).mp h)⟩
    · exact ⟨b,bu,hb⟩
  · exact ⟨a,ha,aw⟩

private theorem nzOne {x : F} : x≠0 → x=1 := by revert x;decide

/-- Fix one more vector by changing the map on a complement to a hyperplane.
The complement vector lies outside the image of the hyperplane, preserving or raising rank. -/
theorem repair_map (f : Endo r) (bad : f≠LinearMap.id) :
    ∃ (g : Endo r) (φ : Vect r →ₗ[F] F) (v : Vect r),
      g=f+φ.smulRight v ∧
      finrank F (range (LinearMap.id-g)) < finrank F (range (LinearMap.id-f)) ∧
      min r (finrank F (range f)+1) ≤ finrank F (range g) := by
  classical
  let K := ker (LinearMap.id-f)
  have km (y) : y∈K ↔ f y=y := by
    change y-f y=0 ↔ f y=y
    rw [sub_eq_zero];exact eq_comm
  have kp : K≠⊤ := by
    intro h
    apply bad;apply LinearMap.ext;intro y
    exact (km y).mp (h ▸ Submodule.mem_top)
  let sing := ¬ Function.Injective f
  obtain ⟨h, hk, hz⟩ : ∃ h, h∉K ∧ (sing → f h=0) := by
    by_cases s : Function.Injective f
    · obtain ⟨h,_,hn⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr kp)
      exact ⟨h,hn,fun hs => False.elim (hs s)⟩
    · have nz : ker f ≠ ⊥ := fun e => s (ker_eq_bot.mp e)
      obtain ⟨h,hin,hn⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr nz)
      have h0 : h≠0 := fun e => hn (by simp [e])
      have z : f h=0 := hin
      exact ⟨h,fun hf => h0 (((km h).mp hf).symm.trans z),fun _ => z⟩
  obtain ⟨φ,nonzero,ann⟩ := Submodule.exists_le_ker_of_notMem hk
  have ph := nzOne nonzero
  let W := ker φ
  have wp : W≠⊤ := by intro eq;exact nonzero (show h∈W from eq ▸ Submodule.mem_top)
  have wm : W.map f≠⊤ := by
    intro eq
    have a := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr wp)
    have b := Submodule.finrank_map_le f W
    rw [eq] at b
    omega
  obtain ⟨x,xw,xf⟩ := outsideBoth W (W.map f) wp wm
  have px : φ x=1 := nzOne xw
  let v := x-f x
  let g := f+φ.smulRight v
  have val (y) : g y=f y+φ y • v := rfl
  have fixx : g x=x := by rw [val,px,one_smul];dsimp [v];abel
  have fixed : K < ker (LinearMap.id-g) := by
    apply lt_of_le_of_ne
    · intro y hy
      have py : φ y=0 := ann hy
      simp [LinearMap.mem_ker,val,py,(km y).mp hy]
    · intro eq;apply xw;apply ann
      rw [eq]
      simp [LinearMap.mem_ker,fixx]
  refine ⟨g,φ,v,rfl,?_,?_⟩
  · have a := Submodule.finrank_lt_finrank_of_lt fixed
    have b := (LinearMap.id-f).finrank_range_add_finrank_ker
    have c := (LinearMap.id-g).finrank_range_add_finrank_ker
    change finrank F (ker (LinearMap.id-f)) < _ at a
    omega
  · by_cases s : Function.Injective f
    · have inj : Function.Injective g := by
        apply LinearMap.ker_eq_bot.mp
        apply le_antisymm _ bot_le
        intro y hy
        change y=0
        have gy : g y=0 := hy
        by_cases p : φ y=0
        · apply s;simpa [val,p] using gy
        · have py := nzOne p
          exfalso
          apply xf
          refine ⟨x-y,?_,?_⟩
          · simp [W,mem_ker,px,py]
          · rw [val,py,one_smul] at gy
            dsimp [v] at gy
            rw [map_sub];abel_nf at gy ⊢ <;> linear_combination (norm := abel) -gy
      have sur := (LinearMap.injective_iff_surjective (f:=g)).mp inj
      rw [range_eq_top.mpr sur,finrank_top,finrank_fin_fun]
      exact min_le_left _ _
    · have fh := hz s
      have incl : range f≤range g := by
        rintro _ ⟨y,rfl⟩
        refine ⟨y-φ y • h,?_⟩
        simp [val,map_sub,map_smul,ph,fh]
      have strict : range f<range g := by
        apply lt_of_le_of_ne incl
        intro eq
        have gh : g h=v := by simp [val,fh,ph]
        have vv : v∈range f := eq ▸ ⟨h,gh⟩
        have xx : x∈range f := by
          convert (range f).add_mem vv (show f x∈range f from ⟨x,rfl⟩) using 1
          dsimp [v];abel
        obtain ⟨y,ey⟩ := xx
        apply xf
        exact ⟨y-φ y • h,by simp [W,mem_ker,ph],by simp [fh,ey]⟩
      have hd := Submodule.finrank_lt_finrank_of_lt strict
      omega
end PEqualNP.Outside.L_meta_33623_aux

namespace PEqualNP.Outside.L_meta_33623_aux
open Matrix LinearMap Module Function

theorem repair_one (A : Sq r) : ∃ B : Sq r, (B-A).rank≤1 ∧
    (1-B).rank≤(1-A).rank-1 ∧ min r (A.rank+1)≤B.rank := by
  classical
  by_cases eq : A=1
  · subst A;refine ⟨1,by simp,by simp,by simp⟩
  let f : Endo r := Matrix.toLin' A
  have ne : f≠LinearMap.id := by
    intro h;apply eq;simpa [f] using congrArg LinearMap.toMatrix' h
  obtain ⟨g,φ,v,gv,drop,grow⟩ := repair_map f ne
  let B : Sq r := LinearMap.toMatrix' g
  have bg : Matrix.toLin' B=g := Matrix.toLin'_toMatrix' g
  have rank_map (M : Sq r) : M.rank=finrank F (LinearMap.range (Matrix.toLin' M)) := rfl
  have db : (1-B).rank=finrank F (LinearMap.range (LinearMap.id-g)) := by rw [rank_map,map_sub,Matrix.toLin'_one,bg]
  have da : (1-A).rank=finrank F (LinearMap.range (LinearMap.id-f)) := by rw [rank_map,map_sub,Matrix.toLin'_one]
  have rb : B.rank=finrank F (LinearMap.range g) := by rw [rank_map,bg]
  have d : B-A=Matrix.vecMulVec v (fun j => φ (Pi.single j 1)) := by
    ext i j
    have h := congrArg (fun (T : Endo r) => T (Pi.single j 1) i) gv
    simp [f,Matrix.mulVec_single_one,LinearMap.smulRight_apply,Pi.smul_apply,smul_eq_mul] at h
    simp only [B,Matrix.sub_apply,LinearMap.toMatrix'_apply,Matrix.vecMulVec_apply]
    rw [h];ring
  exact ⟨B,d ▸ rank_vecMulVec_le _ _,by rw [db,da];omega,by rw [rb];exact grow⟩

noncomputable def repair (A : Sq r) : Sq r := Classical.choose (repair_one A)

theorem after (A : Sq r) (n : Nat) :
    ((repair^[n]) A-A).rank≤n ∧ (1-(repair^[n]) A).rank≤(1-A).rank-n ∧
    min r (A.rank+n)≤((repair^[n]) A).rank := by
  induction n with
  | zero => simp
  | succ n ih =>
    let X := (repair^[n]) A
    have h := Classical.choose_spec (repair_one X)
    change (repair X-X).rank≤1 ∧ (1-repair X).rank≤(1-X).rank-1 ∧ min r (X.rank+1)≤(repair X).rank at h
    rw [Function.iterate_succ_apply']
    have d := dist (repair X) X A
    change (X-A).rank≤n ∧ (1-X).rank≤_ ∧ _≤X.rank at ih
    change (repair X-A).rank≤_ ∧ (1-repair X).rank≤_ ∧ _≤(repair X).rank
    omega

/-- Read the repairs in reverse, grouping the steps into jumps of rank at most d. -/
theorem path_data (H : Sq r) (k d e : Nat) (full : r≤H.rank+d+e) (cost : (1-H).rank≤(k+1)*d+e) :
    ∃ S : Fin (k+2) → Sq r, S 0=1 ∧ ((S (Fin.last _))-H).rank≤e ∧
    ∀ j : Fin (k+1), IsUnit (S j.castSucc) ∧ (S j.castSucc-S j.succ).rank≤d := by
  let time := fun (i : Fin (k+2)) => (k+1-i.val)*d+e
  let S := fun i => (repair^[time i]) H
  have tz : time 0=(k+1)*d+e := by simp [time]
  have tl : time (Fin.last _) =e := by simp [time]
  have z := (after H (time 0)).2.1
  have rz : (1-S 0).rank=0 := by dsimp [S];rw [tz] at z ⊢;omega
  have zeroMat {M : Sq r} (h : M.rank=0) : M=0 := by
    have hh : finrank F (range (Matrix.toLin' M))=0 := h
    have hb : range (Matrix.toLin' M)=⊥ := Submodule.finrank_eq_zero.mp hh
    have h0 := LinearMap.range_eq_bot.mp hb
    simpa using congrArg LinearMap.toMatrix' h0
  refine ⟨S,(sub_eq_zero.mp (zeroMat rz)).symm,?_,?_⟩
  · simpa only [S,tl] using (after H e).1
  · intro j
    have ht : time j.castSucc=d+time j.succ := by
      have := j.isLt
      have ar : k+1-j.val=(k+1-(j.val+1))+1 := by omega
      simp [time,Fin.val_castSucc,Fin.val_succ,ar,Nat.add_mul];omega
    have hd : e≤time j.succ := by simp [time]
    have gr := (after H (time j.castSucc)).2.2
    have hi : (S j.castSucc).rank=r := by
      have up := rank_le_width (S j.castSucc)
      change min r (H.rank+time j.castSucc)≤(S j.castSucc).rank at gr
      omega
    refine ⟨Matrix.mulVec_surjective_iff_isUnit.mp (Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hi)),?_⟩
    change ((repair^[time j.castSucc]) H-(repair^[time j.succ]) H).rank≤d
    rw [ht,Function.iterate_add_apply];exact (after _ d).1
end PEqualNP.Outside.L_meta_33623_aux

namespace PEqualNP.Outside.L_meta_33623_aux
open Matrix
/-- Lift a rank-bounded jump by factoring the difference through the auxiliary coordinates. -/
theorem frame_step {S D : Sq r} (hS : IsUnit S) (jump : (S-D).rank≤d)
    (U : Mat r d) : ∃ U' : Mat r d, ∃ X : Sq r, ∃ Y : Mat d r,
      S*X + U*Y=1 ∧ D*X + U'*Y=1 := by
  obtain ⟨J,V,h⟩ := factor _ jump
  let F := S⁻¹
  have sf : S*F=1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  let G := F*U
  have sg : S*G=U := by rw [show S*G=(S*F)*U by exact (Matrix.mul_assoc ..).symm,sf,Matrix.one_mul]
  let Y := V*F
  refine ⟨D*G+J,F-G*Y,Y,?_,?_⟩
  · rw [Matrix.mul_sub,←Matrix.mul_assoc,sg,sf];abel
  · rw [Matrix.mul_sub,Matrix.add_mul,←Matrix.mul_assoc D G Y]
    have sum : D*F+J*Y=1 := by
      change D*F+J*(V*F)=1
      rw [←Matrix.mul_assoc,←Matrix.add_mul,h]
      have hs : D+(S-D)=S := by abel
      rw [hs,sf]
    rw [←sum];abel

theorem build_frames (S : Fin (k+2) → Sq r) (start : S 0=1)
    (step : ∀ j : Fin (k+1),IsUnit (S j.castSucc) ∧ (S j.castSucc-S j.succ).rank≤d) :
    Frames k r (r+d) (S (Fin.last _)) := by
  classical
  have opts (j : Fin (k+1)) (u : Mat r d) := frame_step (step j).1 (step j).2 u
  let U : Fin (k+2) → Mat r d := Fin.induction 0 (fun j u => Classical.choose (opts j u))
  let x := fun j => Classical.choose (Classical.choose_spec (opts j (U j.castSucc)))
  let y := fun j => Classical.choose (Classical.choose_spec (Classical.choose_spec (opts j (U j.castSucc))))
  let X : Fin (k+2) → Sq r := Fin.cases 1 x
  let Y : Fin (k+2) → Mat d r := Fin.cases 0 y
  have formulas (j : Fin (k+1)) : S j.castSucc * X j.succ + U j.castSucc * Y j.succ=1 ∧
      S j.succ * X j.succ + U j.succ * Y j.succ=1 := by
    simpa only [X,Y,Fin.cases_succ,U,Fin.induction_succ,x,y] using
      Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (opts j (U j.castSucc))))
  let equiv : Fin (r+d) ≃ (Fin r ⊕ Fin d) := finSumFinEquiv.symm
  let A := fun i => (Matrix.fromCols (S i) (U i)).submatrix id equiv
  let B := fun j => (Matrix.fromRows (X j) (Y j)).submatrix equiv id
  have mul (i j) : A i*B j=S i*X j+U i*Y j := by
    simp only [A,B,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id,Matrix.fromCols_mul_fromRows]
  refine ⟨A,B,?_,fun j => (mul _ _).trans (formulas j).1,?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simp [mul,X,Y,start]
    | succ j => exact (mul _ _).trans (formulas j).2
  · simp [mul,X,Y]

theorem rank_budget (H : Sq r) (w e k : Nat) :
    (∃ S : Sq r,Frames k r w S ∧ (S-H).rank≤e) ↔
    r≤w ∧ r≤H.rank+(w-r)+e ∧ (1-H).rank≤(k+1)*(w-r)+e := by
  constructor
  · rintro ⟨S,f,err⟩
    obtain ⟨rw,h,d⟩ := necessary f
    have sh := addRank (S-H) H
    rw [sub_add_cancel] at sh
    have one := dist 1 S H
    exact ⟨rw,by omega,by omega⟩
  · rintro ⟨rw,h,d⟩
    obtain ⟨S,start,err,steps⟩ := path_data H k (w-r) e h d
    exact ⟨_,Nat.add_sub_of_le rw ▸ build_frames S start steps,err⟩
end PEqualNP.Outside.L_meta_33623_aux

open PEqualNP.Outside.L_meta_33623_aux

theorem PEqualNP.Outside.L_meta_33623 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (Q : PEqualNP.CircuitLowerBounds.Circuit) =>
  (Q.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD Q.output 0
∀ (n m k r t e : ℕ) (T : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
  let I := Fin (k+2)
  let M := Matrix (Fin r) (Fin r) (ZMod 2)
  let last : I := Fin.last (k+1)
  ∀ (rows : I × Fin r ↪ Fin n) (cols : I × Fin r ↪ Fin m)
    (_ : ∀ z, rows z ≠ u) (_ : ∀ z, cols z ≠ v) (L R : I → M) (H : M),
    let block := fun (P : Fin n → Fin m → Bool) (i j : I) =>
      (fun a b => ((P (rows (i,a)) (cols (j,b))).toNat : ZMod 2) +
        ((P u (cols (j,b))).toNat : ZMod 2) + ((P (rows (i,a)) v).toNat : ZMod 2) +
        ((P u v).toNat : ZMod 2) : M)
    (∀ i, IsUnit (L i) ∧ IsUnit (R i)) →
    (∀ i, block T i i = L i * R i) →
    (∀ j : Fin (k+1), block T j.castSucc j.succ = L j.castSucc * R j.succ) →
    block T last 0 = L last * H * R 0 →
    ((∃ (P : Fin n → Fin m → Bool) (Q : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) Q ∧
      PEqualNP.Represents.Represents P Q ∧ depth (n+m) Q ≤ 1 ∧ Q.gates.countP nonlinear ≤ t ∧
      (∀ i, P i v = T i v) ∧ (∀ j, P u j = T u j) ∧
      (∀ i, block P i i = block T i i) ∧
      (∀ j : Fin (k+1), block P j.castSucc j.succ = block T j.castSucc j.succ) ∧
      ∃ X Y : Fin e → Finset (Fin r), ∀ a b : Fin r,
        xor (P (rows (last,a)) (cols (0,b))) (T (rows (last,a)) (cols (0,b))) =
          decide ((Finset.univ.filter (fun j : Fin e => a ∈ X j ∧ b ∈ Y j)).card % 2 = 1)) ↔
    r ≤ 2*t ∧ r ≤ Matrix.rank H + (2*t-r) + e ∧ Matrix.rank (1-H) ≤ (k+1)*(2*t-r)+e)
) := by
  intro nonlinear depth n m k r t e T u v I M last rows cols ru cv L R H blockT units diag next close
  rw [←rank_budget H (2*t) e k, ←panel_iff rows cols u v ru cv T L R H units diag next close]
  constructor
  · rintro ⟨P,C,fan,back,rep,dep,count,col,row,pd,pn,err⟩
    exact ⟨P,(criterion P u v t).mpr ⟨C,⟨fan,back,rep⟩,dep,count⟩,col,row,pd,pn,err⟩
  · rintro ⟨P,rank,col,row,pd,pn,err⟩
    obtain ⟨C,⟨fan,back,rep⟩,dep,count⟩ := (criterion P u v t).mp rank
    exact ⟨P,C,fan,back,rep,dep,count,col,row,pd,pn,err⟩
