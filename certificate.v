(***************************************************************)
(*                                                             *)
(*  Coq script (certificate) accompanying IMR submission       *)
(*    "Certified Functions for Mesh Generation"                *)
(*                                                             *)
(*  Copyright (C) 2019                                         *)
(*    (Author's name and affiliation anonymized                *)
(*     for IMR review purposes and will appear upon            *)
(*     publication.)                                           *)
(*                                                             *)
(***************************************************************)
(*                                                             *)
(*  This work is licensed under the Creative Commons           *)
(*    Attribution-NonCommercial-ShareAlike 4.0 International   *)
(*    License. To view a copy of this license, visit           *)
(*    http://creativecommons.org/licenses/by-nc-sa/4.0/        *)
(*    or send a letter to                                      *)
(*    Creative Commons, PO Box 1866,                           *)
(*    Mountain View, CA 94042, USA.                            *)
(*                                                             *)
(***************************************************************)


Require Export List BinPosDef Omega.
Export ListNotations.

Inductive Coord3 := 
  C3 : Z -> Z -> Z -> Coord3.

Inductive Sign := Inside | Outside | Boundary.

Inductive StructuredTetCase := 
  Tet_I1 | Tet_I2 | Tet_I3 | Tet_I4 | 
  Tet_J1 | Tet_J2 | Tet_J3 | Tet_J4 | 
  Tet_K1 | Tet_K2 | Tet_K3 | Tet_K4.

Inductive StructuredTetId :=
  STId : Coord3 -> StructuredTetCase 
         -> StructuredTetId.

Definition VertexOrder : Type := 
  Coord3 -> Coord3 -> Coord3 -> Coord3 ->
  (Coord3 * Coord3 * Coord3 * Coord3).

Inductive StructuredTet :=
  ST : Coord3 -> Coord3 -> Coord3 -> Coord3 -> 
       StructuredTetId * VertexOrder -> 
       StructuredTetId * VertexOrder ->
       StructuredTetId * VertexOrder -> 
       StructuredTetId * VertexOrder -> 
       StructuredTet.

Local Open Scope Z_scope.

Definition GetStructuredTet (tid : StructuredTetId)
                            : StructuredTet :=
  let P0123 v0 v1 v2 v3 := (v0, v1, v2, v3) in
  let P1032 v0 v1 v2 v3 := (v1, v0, v3, v2) in
  match tid with STId (C3 i j k) t =>
    let i1 := i + 1 in
    let j1 := j + 1 in
    let k1 := k + 1 in
    let i2 := i + 2 in
    let j2 := j + 2 in
    let k2 := k + 2 in
    let i3 := i + 3 in
    let j3 := j + 3 in
    let k3 := k + 3 in
    let v000 := C3 i  j  k in
    let v200 := C3 i2 j  k in
    let v020 := C3 i  j2 k in
    let v220 := C3 i2 j2 k in
    let v002 := C3 i  j  k2 in
    let v202 := C3 i2 j  k2 in
    let v022 := C3 i  j2 k2 in
    let v222 := C3 i2 j2 k2 in
    let v111 := C3 i1 j1 k1 in
    let v311 := C3 i3 j1 k1 in
    let v131 := C3 i1 j3 k1 in
    let v331 := C3 i3 j3 k1 in
    let v113 := C3 i1 j1 k3 in
    let v313 := C3 i3 j1 k3 in
    let v133 := C3 i1 j3 k3 in
    let v333 := C3 i3 j3 k3 in
    let i2' := i - 2 in
    let j2' := j - 2 in
    let k2' := k - 2 in
    match t with
    | Tet_I1 => 
        ST v022 v222 v131 v111 
           (STId v000 Tet_K4, P0123) 
           (STId (C3 i2' j k) Tet_K1, P1032)
           (STId v000 Tet_I3, P0123)
           (STId v000 Tet_I2, P0123)
    | Tet_I2 => 
        ST v022 v222 v131 v133
           (STId (C3 i j2 k) Tet_J2, P1032)
           (STId (C3 i2' j2 k) Tet_J3, P0123)
           (STId v000 Tet_I4, P0123)
           (STId v000 Tet_I1, P0123)
    | Tet_I3 => 
        ST v022 v222 v113 v111
           (STId v000 Tet_J2, P0123)
           (STId (C3 i2' j k) Tet_J3, P1032)
           (STId v000 Tet_I1, P0123)
           (STId v000 Tet_I4, P0123)
    | Tet_I4 => 
        ST v022 v222 v113 v133
           (STId (C3 i j k2) Tet_K4, P1032)
           (STId (C3 i2' j k2) Tet_K1, P0123)
           (STId v000 Tet_I2, P0123)
           (STId v000 Tet_I3, P0123)
    | Tet_J1 => 
        ST v202 v222 v113 v313
           (STId (C3 i j k2) Tet_K2, P1032)
           (STId (C3 i j2' k2) Tet_K3, P0123)
           (STId v000 Tet_J3, P0123)
           (STId v000 Tet_J2, P0123)
    | Tet_J2 => 
        ST v202 v222 v113 v111
           (STId v000 Tet_I3, P0123)
           (STId (C3 i j2' k) Tet_I2, P1032)
           (STId v000 Tet_J4, P0123)
           (STId v000 Tet_J1, P0123)
    | Tet_J3 => 
        ST v202 v222 v311 v313
           (STId (C3 i2 j k) Tet_I3, P1032)
           (STId (C3 i2 j2' k) Tet_I2, P0123)
           (STId v000 Tet_J1, P0123)
           (STId v000 Tet_J4, P0123)
    | Tet_J4 => 
        ST v202 v222 v311 v111
           (STId v000 Tet_K2, P0123)
           (STId (C3 i j2' k) Tet_K3, P1032)
           (STId v000 Tet_J2, P0123)
           (STId v000 Tet_J3, P0123)
    | Tet_K1 => 
        ST v220 v222 v311 v331
           (STId (C3 i2 j k) Tet_I1, P1032)
           (STId (C3 i2 j k2') Tet_I4, P0123)
           (STId v000 Tet_K3, P0123)
           (STId v000 Tet_K2, P0123)
    | Tet_K2 => 
        ST v220 v222 v311 v111
           (STId v000 Tet_J4, P0123)
           (STId (C3 i j k2') Tet_J1, P1032)
           (STId v000 Tet_K4, P0123)
           (STId v000 Tet_K1, P0123)
    | Tet_K3 => 
        ST v220 v222 v131 v331
           (STId (C3 i j2 k) Tet_J4, P1032)
           (STId (C3 i j2 k2') Tet_J1, P0123)
           (STId v000 Tet_K1, P0123)
           (STId v000 Tet_K4, P0123)
    | Tet_K4 => 
        ST v220 v222 v131 v111 
           (STId v000 Tet_I1, P0123)
           (STId (C3 i j k2') Tet_I4, P1032)
           (STId v000 Tet_K2, P0123)
           (STId v000 Tet_K3, P0123)
    end
  end.

Local Close Scope Z_scope.


Section Get_Unstructured_Tets.

  Variable Vertex : Type.
  Variable GetSign : Vertex -> Sign.
  Variable GetIntersection : 
             Vertex -> Vertex -> Vertex.

  Inductive UnstructuredTet :=
    UT : Vertex -> Vertex -> 
         Vertex -> Vertex -> UnstructuredTet.

  Definition GetUnstructuredTets 
               (v1 v2 v3 v4 : Vertex) 
               : list UnstructuredTet :=

    let II_IO u1 u2 u3 m14 m24 m34 :=
      [UT u1 u2 u3 m34; UT u1 u2 m34 m14; 
       UT u2 m34 m14 m24] in

    let II_BO u1 u2 u3 m14 m24 :=
      [UT u1 u2 u3 m14; UT m14 u2 u3 m24] in

    let II_OO u1 u2 m13 m14 m23 m24 :=
      [UT u2 m23 m14 m24; UT u1 u2 m23 m14; 
       UT u1 m14 m23 m13] in

    let IB_IO u1 u2 u3 m14 m34 :=
      [UT u1 u3 u2 m34; UT u1 m34 u2 m14] in

    let IO_IO u1 u3 m12 m14 m23 m34 :=
      [UT u1 m34 m12 u3; UT u1 m14 m12 m34; 
       UT m12 m34 u3 m23] in

    let IBBO u1 u2 u3 m14 :=
      [UT u1 u2 u3 m14] in

    let IBOO u1 u2 m13 m14 :=
      [UT u1 u2 m13 m14] in

    let IOOO u1 m12 m13 m14 :=
      [UT m14 m13 m12 u1] in

    let b := GetIntersection in
    
    match GetSign v1, GetSign v2, GetSign v3, GetSign v4 with
    | Inside  , Inside  , Inside  , Inside   => [UT v1 v2 v3 v4]
    | Inside  , Inside  , Inside  , Boundary => [UT v1 v2 v3 v4]
    | Inside  , Inside  , Inside  , Outside  => II_IO v1 v2 v3 (b v1 v4) (b v2 v4) (b v3 v4)
    | Inside  , Inside  , Boundary, Inside   => [UT v1 v2 v3 v4]
    | Inside  , Inside  , Boundary, Boundary => [UT v1 v2 v3 v4]
    | Inside  , Inside  , Boundary, Outside  => II_BO v1 v2 v3 (b v1 v4) (b v2 v4)
    | Inside  , Inside  , Outside , Inside   => II_IO v2 v1 v4 (b v2 v3) (b v1 v3) (b v4 v3)
    | Inside  , Inside  , Outside , Boundary => II_BO v2 v1 v4 (b v2 v3) (b v1 v3)
    | Inside  , Inside  , Outside , Outside  => II_OO v1 v2 (b v1 v3) (b v1 v4) (b v2 v3) (b v2 v4)

    | Inside  , Boundary, Inside  , Inside   => [UT v1 v2 v3 v4]
    | Inside  , Boundary, Inside  , Boundary => [UT v1 v2 v3 v4]
    | Inside  , Boundary, Inside  , Outside  => IB_IO v1 v2 v3 (b v1 v4) (b v3 v4)
    | Inside  , Boundary, Boundary, Inside   => [UT v1 v2 v3 v4]
    | Inside  , Boundary, Boundary, Boundary => [UT v1 v2 v3 v4]
    | Inside  , Boundary, Boundary, Outside  => IBBO v1 v2 v3 (b v1 v4)
    | Inside  , Boundary, Outside , Inside   => IB_IO v1 v2 v4 (b v1 v3) (b v4 v3)
    | Inside  , Boundary, Outside , Boundary => IBBO v1 v2 v4 (b v1 v3)
    | Inside  , Boundary, Outside , Outside  => IBOO v1 v2 (b v1 v3) (b v1 v4)

    | Inside  , Outside , Inside  , Inside   => II_IO v3 v4 v1 (b v3 v2) (b v4 v2) (b v1 v2)
    | Inside  , Outside , Inside  , Boundary => IB_IO v3 v4 v1 (b v3 v2) (b v1 v2)
    | Inside  , Outside , Inside  , Outside  => IO_IO v1 v3 (b v1 v2) (b v1 v4) (b v3 v2) (b v3 v4)
    | Inside  , Outside , Boundary, Inside   => IB_IO v4 v3 v1 (b v4 v2) (b v1 v2)
    | Inside  , Outside , Boundary, Boundary => IBBO v1 v3 v4 (b v1 v2)
    | Inside  , Outside , Boundary, Outside  => IBOO v1 v3 (b v1 v2) (b v1 v4)
    | Inside  , Outside , Outside , Inside   => IO_IO v1 v4 (b v1 v2) (b v1 v3) (b v4 v2) (b v4 v3)
    | Inside  , Outside , Outside , Boundary => IBOO v1 v4 (b v1 v2) (b v1 v3)
    | Inside  , Outside , Outside , Outside  => IOOO v1 (b v1 v2) (b v1 v3) (b v1 v4)

    | Boundary, Inside  , Inside  , Inside   => [UT v1 v2 v3 v4]
    | Boundary, Inside  , Inside  , Boundary => [UT v1 v2 v3 v4]
    | Boundary, Inside  , Inside  , Outside  => IB_IO v2 v1 v3 (b v2 v4) (b v3 v4)
    | Boundary, Inside  , Boundary, Inside   => [UT v1 v2 v3 v4]
    | Boundary, Inside  , Boundary, Boundary => [UT v1 v2 v3 v4]
    | Boundary, Inside  , Boundary, Outside  => IBBO v2 v1 v3 (b v2 v4)
    | Boundary, Inside  , Outside , Inside   => IB_IO v2 v1 v4 (b v2 v3) (b v4 v3)
    | Boundary, Inside  , Outside , Boundary => IBBO v2 v1 v4 (b v2 v3)
    | Boundary, Inside  , Outside , Outside  => IBOO v2 v1 (b v2 v3) (b v2 v4)

    | Boundary, Boundary, Inside  , Inside   => [UT v1 v2 v3 v4]
    | Boundary, Boundary, Inside  , Boundary => [UT v1 v2 v3 v4]
    | Boundary, Boundary, Inside  , Outside  => IBBO v3 v1 v2 (b v3 v4)
    | Boundary, Boundary, Boundary, Inside   => [UT v1 v2 v3 v4]
    | Boundary, Boundary, Boundary, Boundary => []
    | Boundary, Boundary, Boundary, Outside  => []
    | Boundary, Boundary, Outside , Inside   => IBBO v4 v1 v2 (b v4 v3)
    | Boundary, Boundary, Outside , Boundary => []
    | Boundary, Boundary, Outside , Outside  => []

    | Boundary, Outside , Inside  , Inside   => II_BO v3 v4 v1 (b v3 v2) (b v4 v2)
    | Boundary, Outside , Inside  , Boundary => IBBO v3 v1 v4 (b v3 v2)
    | Boundary, Outside , Inside  , Outside  => IBOO v3 v1 (b v3 v2) (b v3 v4)
    | Boundary, Outside , Boundary, Inside   => IBBO v4 v1 v3 (b v4 v2)
    | Boundary, Outside , Boundary, Boundary => []
    | Boundary, Outside , Boundary, Outside  => []
    | Boundary, Outside , Outside , Inside   => IBOO v4 v1 (b v4 v2) (b v4 v3)
    | Boundary, Outside , Outside , Boundary => []
    | Boundary, Outside , Outside , Outside  => []

    | Outside , Inside  , Inside  , Inside   => II_IO v4 v3 v2 (b v4 v1) (b v3 v1) (b v2 v1)
    | Outside , Inside  , Inside  , Boundary => IB_IO v3 v4 v2 (b v3 v1) (b v2 v1)
    | Outside , Inside  , Inside  , Outside  => IO_IO v2 v3 (b v2 v1) (b v2 v4) (b v3 v1) (b v3 v4)
    | Outside , Inside  , Boundary, Inside   => IB_IO v4 v3 v2 (b v4 v1) (b v2 v1)
    | Outside , Inside  , Boundary, Boundary => IBBO v2 v3 v4 (b v2 v1)
    | Outside , Inside  , Boundary, Outside  => IBOO v2 v3 (b v2 v1) (b v2 v4)
    | Outside , Inside  , Outside , Inside   => IO_IO v2 v4 (b v2 v1) (b v2 v3) (b v4 v1) (b v4 v3)
    | Outside , Inside  , Outside , Boundary => IBOO v2 v4 (b v2 v1) (b v2 v3)
    | Outside , Inside  , Outside , Outside  => IOOO v2 (b v2 v1) (b v2 v3) (b v2 v4)

    | Outside , Boundary, Inside  , Inside   => II_BO v4 v3 v2 (b v4 v1) (b v3 v1)
    | Outside , Boundary, Inside  , Boundary => IBBO v3 v2 v4 (b v3 v1)
    | Outside , Boundary, Inside  , Outside  => IBOO v3 v2 (b v3 v1) (b v3 v4)
    | Outside , Boundary, Boundary, Inside   => IBBO v4 v2 v3 (b v4 v1)
    | Outside , Boundary, Boundary, Boundary => []
    | Outside , Boundary, Boundary, Outside  => []
    | Outside , Boundary, Outside , Inside   => IBOO v4 v2 (b v4 v1) (b v4 v3)
    | Outside , Boundary, Outside , Boundary => []
    | Outside , Boundary, Outside , Outside  => []

    | Outside , Outside , Inside  , Inside   => II_OO v3 v4 (b v3 v1) (b v3 v2) (b v4 v1) (b v4 v2)
    | Outside , Outside , Inside  , Boundary => IBOO v3 v4 (b v3 v1) (b v3 v2)
    | Outside , Outside , Inside  , Outside  => IOOO v3 (b v3 v1) (b v3 v2) (b v3 v4)
    | Outside , Outside , Boundary, Inside   => IBOO v4 v3 (b v4 v1) (b v4 v2)
    | Outside , Outside , Boundary, Boundary => []
    | Outside , Outside , Boundary, Outside  => []
    | Outside , Outside , Outside , Inside   => IOOO v4 (b v4 v1) (b v4 v2) (b v4 v3)
    | Outside , Outside , Outside , Boundary => []
    | Outside , Outside , Outside , Outside  => []
    end.

End Get_Unstructured_Tets.


Section GetStructuredTet_Spec.

  Variables (v1 v2 v3 v4 : Coord3)
            (nei_tid : StructuredTetId)
            (nei_order : VertexOrder).

  Definition U := 
    match GetStructuredTet nei_tid with 
      ST u1 u2 u3 u4 _ _ _ _ => 
        nei_order u1 u2 u3 u4
    end.

  Definition Face1Correct := 
    match U with (u1, u2, u3, u4) => 
      ~(v1 = u1) /\ (v2 = u2) /\ 
      (v3 = u3) /\ (v4 = u4)
    end.

  Definition Face2Correct := 
    match U with (u1, u2, u3, u4) => 
      (v1 = u1) /\ ~(v2 = u2) /\ 
      (v3 = u3) /\ (v4 = u4)
    end.

  Definition Face3Correct := 
    match U with (u1, u2, u3, u4) => 
      (v1 = u1) /\ (v2 = u2) /\ 
      ~(v3 = u3) /\ (v4 = u4)
    end.

  Definition Face4Correct := 
    match U with (u1, u2, u3, u4) => 
      (v1 = u1) /\ (v2 = u2) /\ 
      (v3 = u3) /\ ~(v4 = u4)
    end.

End GetStructuredTet_Spec.


Local Open Scope Z_scope.

Lemma Zplus_minus_comm : forall a b c : Z,
  a - b + c = a + (c - b).
Proof. intros. omega. Qed.

Section GetStructuredTet_Proof.

  Hint Rewrite 
    Zplus_minus_comm Zplus_assoc_reverse
    Z.add_0_r Z.add_opp_r : Rewrite1.

  Hint Extern 5 (~_) => 
    red; intros H; inversion H; omega.

  Theorem FacesCorrect : 
    forall tid : StructuredTetId,
    match GetStructuredTet tid with
      ST v1 v2 v3 v4 (tid1, o1) (tid2, o2) 
                     (tid3, o3) (tid4, o4) =>
        (Face1Correct v1 v2 v3 v4 tid1 o1) /\ 
        (Face2Correct v1 v2 v3 v4 tid2 o2) /\ 
        (Face3Correct v1 v2 v3 v4 tid3 o3) /\ 
        (Face4Correct v1 v2 v3 v4 tid4 o4)
    end.
  Proof.
    intros [[i j k] t];
    unfold Face1Correct, Face2Correct, 
           Face3Correct, Face4Correct, U;
    destruct t;
    unfold GetStructuredTet;
    autorewrite with Rewrite1;
    repeat (split; auto 20).
  Qed.

End GetStructuredTet_Proof.

Local Close Scope Z_scope.


Inductive BCoord := Zero | Interior | One.

Inductive Below : BCoord -> BCoord -> 
                  BCoord -> Prop :=
  | B_1 : Below Zero Zero Interior
  | B_2 : Below Zero Zero One
  | B_3 : Below Zero Interior Interior
  | B_4 : Below Zero Interior One.

Inductive Above : BCoord -> BCoord -> 
                  BCoord -> Prop :=
  | A_1 : Above One Zero Interior
  | A_2 : Above One Zero One
  | A_3 : Above One Interior Interior
  | A_4 : Above One Interior One.


Section Below_Above_Symm.
  Variables c a b : BCoord.
  Inductive BelowSymm : Prop :=
  | BS_1 : Below c a b -> BelowSymm
  | BS_2 : Below c b a -> BelowSymm.
  Inductive AboveSymm : Prop :=
  | AS_1 : Above c a b -> AboveSymm
  | AS_2 : Above c b a -> AboveSymm.
End Below_Above_Symm.

Section Segment_Point_Not_Interiorersecting_1D.
  Variables c a b : BCoord.
  Inductive SPNI1D : Prop :=
  | SPNI1D_1 : BelowSymm c a b -> SPNI1D
  | SPNI1D_2 : AboveSymm c a b -> SPNI1D.
End Segment_Point_Not_Interiorersecting_1D.

Section Segment_Point_Not_Interiorersecting_3D.
  Variables a1 a2 a3 b1 b2 b3 c1 c2 c3 : BCoord.
  Inductive SPNI3D : Prop :=
  | SPNI3D_1 : SPNI1D c1 a1 b1 -> SPNI3D
  | SPNI3D_2 : SPNI1D c2 a2 b2 -> SPNI3D
  | SPNI3D_3 : SPNI1D c3 a3 b3 -> SPNI3D.
End Segment_Point_Not_Interiorersecting_3D.

Section Segment_Segment_Not_Interiorersecting_1D.
  Variables a b c d : BCoord.
  Inductive SSNI1D : Prop :=
  | SSNI1D_1 : BelowSymm a c d -> 
               BelowSymm b c d -> SSNI1D
  | SSNI1D_2 : BelowSymm c a b -> 
               BelowSymm d a b -> SSNI1D.
End Segment_Segment_Not_Interiorersecting_1D.

Section Segment_Segment_Not_Interiorersecting_3D.
  Variables a1 a2 a3 b1 b2 b3 
            c1 c2 c3 d1 d2 d3 : BCoord.
  Inductive SSNI3D : Prop :=
  | SSNI3D_1 : SSNI1D a1 b1 c1 d1 -> SSNI3D
  | SSNI3D_2 : SSNI1D a2 b2 c2 d2 -> SSNI3D
  | SSNI3D_3 : SSNI1D a3 b3 c3 d3 -> SSNI3D.
End Segment_Segment_Not_Interiorersecting_3D.


Section GetUnstructuredTets_Spec.

  Variable Vertex : Type.
  Variable GetSign : Vertex -> Sign.
  Variable GetIntersection : Vertex -> Vertex -> Vertex.

  Definition Edge : Type := Vertex * Vertex.

  Definition Edges (t : UnstructuredTet Vertex) 
             : list Edge :=
    match t with UT _ u v w r => 
      [(u, v); (u, w); (u, r); (v, w); (v, r); (w, r)]
    end.

  Variables f1 f2 f3 p q : Vertex.

  Inductive FCoord : Vertex -> BCoord -> 
                     BCoord -> BCoord -> Prop :=
    | FC_1 : FCoord f1 One Zero Zero
    | FC_2 : FCoord f2 Zero One Zero
    | FC_3 : FCoord f3 Zero Zero One
    | FC_4 : FCoord (GetIntersection f1 f2)
                    Interior Interior Zero
    | FC_5 : FCoord (GetIntersection f2 f1)
                    Interior Interior Zero
    | FC_6 : FCoord (GetIntersection f1 f3)
                    Interior Zero Interior
    | FC_7 : FCoord (GetIntersection f3 f1)
                    Interior Zero Interior
    | FC_8 : FCoord (GetIntersection f2 f3)
                    Zero Interior Interior
    | FC_9 : FCoord (GetIntersection f3 f2)
                    Zero Interior Interior.

  Inductive PCoord : Vertex -> Prop :=
    | PC_1 : PCoord p
    | PC_2 : PCoord (GetIntersection p f1)
    | PC_3 : PCoord (GetIntersection f1 p)
    | PC_4 : PCoord (GetIntersection p f2)
    | PC_5 : PCoord (GetIntersection f2 p)
    | PC_6 : PCoord (GetIntersection p f3)
    | PC_7 : PCoord (GetIntersection f3 p).

  Inductive QCoord : Vertex -> Prop :=
    | QC_1 : QCoord q
    | QC_2 : QCoord (GetIntersection q f1)
    | QC_3 : QCoord (GetIntersection f1 q)
    | QC_4 : QCoord (GetIntersection q f2)
    | QC_5 : QCoord (GetIntersection f2 q)
    | QC_6 : QCoord (GetIntersection q f3)
    | QC_7 : QCoord (GetIntersection f3 q).

  Section Special_Vertex.
    Variables (v u1 u2 : Vertex) 
              (V : Vertex -> Prop).
    Inductive SpecialVertex : Prop :=
    | SV_1 : v = u1 -> SpecialVertex
    | SV_2 : v = u2 -> SpecialVertex
    | SV_3 : V v -> SpecialVertex.
  End Special_Vertex.

  Section Not_In.
    Variables (v u1 u2 : Vertex) 
              (V U : Vertex -> Prop).
    Inductive NotIn : Prop :=
    | NI_1 : SpecialVertex v u1 u2 V -> NotIn
    | NI_2 : U u1 -> NotIn
    | NI_3 : U u2 -> NotIn
    | NI_4 : forall a1 a2 a3 b1 b2 b3 c1 c2 c3 : BCoord, 
             FCoord u1 a1 a2 a3 -> 
             FCoord u2 b1 b2 b3 -> 
             FCoord v c1 c2 c3 ->
             SPNI3D a1 a2 a3 b1 b2 b3 c1 c2 c3 ->
             NotIn.
  End Not_In.

  Section Two_Edges_Compatible.
    Variables p1 p2 q1 q2 : Vertex.
    Inductive TwoEdgesCompatible : Prop :=
    | EC_1 : SpecialVertex p1 q1 q2 PCoord -> 
             NotIn p2 q1 q2 PCoord QCoord -> 
             TwoEdgesCompatible
    | EC_2 : SpecialVertex p2 q1 q2 PCoord -> 
             NotIn p1 q1 q2 PCoord QCoord -> 
             TwoEdgesCompatible
    | EC_3 : SpecialVertex q1 p1 p2 QCoord -> 
             NotIn q2 p1 p2 QCoord PCoord -> 
             TwoEdgesCompatible
    | EC_4 : SpecialVertex q2 p1 p2 QCoord -> 
             NotIn q1 p1 p2 QCoord PCoord -> 
             TwoEdgesCompatible
    | EC_5 : forall a1 a2 a3 b1 b2 b3 
                    c1 c2 c3 d1 d2 d3 : BCoord, 
             FCoord p1 a1 a2 a3 -> 
             FCoord p2 b1 b2 b3 ->
             FCoord q1 c1 c2 c3 -> 
             FCoord q2 d1 d2 d3 ->
             SSNI3D a1 a2 a3 b1 b2 b3 
                    c1 c2 c3 d1 d2 d3 ->
             TwoEdgesCompatible.
  End Two_Edges_Compatible.

  Definition EdgePairCompatible ee :=
    let '((p1, p2), (q1, q2)) := ee in 
    TwoEdgesCompatible p1 p2 q1 q2.

  Definition AllEdgesCompatible 
             (u1 u2 u3 u4 v1 v2 v3 v4 : Vertex)
             : Prop :=
    let T := GetUnstructuredTets Vertex 
               GetSign GetIntersection in
    forall (t1 t2 : UnstructuredTet Vertex),
    List.In t1 (T u1 u2 u3 u4) -> 
    List.In t2 (T v1 v2 v3 v4) -> 
    Forall EdgePairCompatible 
           (list_prod (Edges t1) (Edges t2)).

End GetUnstructuredTets_Spec.


Section GetUnstructuredTets_Proof.

  Hint Constructors 
    Below BelowSymm Above AboveSymm SPNI1D SPNI3D
    SSNI1D SSNI3D FCoord PCoord QCoord 
    SpecialVertex NotIn TwoEdgesCompatible.

  Ltac Proof1 := time
    match goal with
      [ |- AllEdgesCompatible _ ?GetSign _ 
             ?f1 ?f2 ?f3 ?p ?q _ _ _ _ _ _ _ _  ] => 
        unfold AllEdgesCompatible;
        intros t1 t2 H1 H2;
        apply Forall_forall;
        destruct t1 as [u1 u2 u3 u4], t2 as [v1 v2 v3 v4];
        unfold Edges;
        unfold list_prod;
        unfold List.map;
        simpl;
        unfold GetUnstructuredTets in H1, H2;
        intros ee H3;
        destruct (GetSign p) eqn: CP,
                 (GetSign f1) eqn: CF1,
                 (GetSign f2) eqn: CF2,
                 (GetSign f3) eqn: CF3,
                 (GetSign q) eqn: CQ; 
        unfold List.In in H1, H2;
        firstorder;
        match goal with [H: _, H0: _, H1: _ |- _] =>
          try rewrite <- H; 
          try (inversion H0 as [[V1 V2 V3 V4]]; 
              try rewrite <- V1; try rewrite <- V2; 
              try rewrite <- V3; try rewrite <- V4);
          try (inversion H1 as [[U1 U2 U3 U4]]; 
              try rewrite <- U1; try rewrite <- U2; 
              try rewrite <- U3; try rewrite <- U4);
          unfold EdgePairCompatible;
          eauto 20
        end
    end.

  Lemma CompatibilityOrders : 
    forall Vertex GetSign GetIntersection f1 f2 f3 p q,
    let P := AllEdgesCompatible Vertex GetSign 
             GetIntersection f1 f2 f3 p q in
    P p f1 f2 f3 q f1 f2 f3 /\ 
    P p f1 f2 f3 f1 q f3 f2 /\
    P f1 p f2 f3 q f1 f3 f2 /\
    P f1 p f2 f3 f1 q f2 f3 /\
    P f1 f2 p f3 f1 f2 q f3 /\
    P f1 f2 f3 p f1 f2 f3 q.
   (* This proof takes about an hour to execute 
    on a MacBook Pro equipped with Intel Core i9
    @ 2.4 GHz processor. *)
  Proof.
    repeat split.
    Proof1. Proof1. Proof1. Proof1. Proof1. Proof1.
  Qed.

End GetUnstructuredTets_Proof.


Section Structured_Unstructured_Proof.

  Hint Rewrite 
    Zplus_minus_comm Zplus_assoc_reverse 
    Z.add_0_r Z.add_opp_r : Rewrite1.

  Ltac Proof2 :=
    intros GetSign GetIntersection [[i j k] t]; 
    destruct t;
    unfold GetStructuredTet; 
    autorewrite with Rewrite1; 
    simpl;
    apply CompatibilityOrders.

  Theorem Face1Compatible : 
    forall GetSign GetIntersection tid,
    match GetStructuredTet tid with
      ST v1 v2 v3 v4 (tid1, order1) _ _ _ =>
        match GetStructuredTet tid1 with 
          ST u1 u2 u3 u4 _ _ _ _ =>
            let '(w1, w2, w3, w4) := 
              order1 u1 u2 u3 u4 in
            AllEdgesCompatible Coord3 GetSign 
              GetIntersection w2 w3 w4 v1 w1 
              v1 v2 v3 v4 u1 u2 u3 u4
        end
    end.
  Proof. Proof2.  Qed.

  Theorem Face2Compatible :
    forall GetSign GetIntersection tid,
    match GetStructuredTet tid with
      ST v1 v2 v3 v4 _ (tid2, order2) _ _ =>
        match GetStructuredTet tid2 with
          ST u1 u2 u3 u4 _ _ _ _ =>
            let '(w1, w2, w3, w4) := 
              order2 u1 u2 u3 u4 in
            AllEdgesCompatible Coord3 GetSign
              GetIntersection w1 w3 w4 v2 w2 v1 v2 v3 v4
              u1 u2 u3 u4
        end
    end.
  Proof. Proof2.  Qed.

  Theorem Face3Compatible : 
    forall GetSign GetIntersection tid,
    match GetStructuredTet tid with
      ST v1 v2 v3 v4 _ _ (tid3, order3) _ =>
        match GetStructuredTet tid3 with 
          ST u1 u2 u3 u4 _ _ _ _ =>
            let '(w1, w2, w3, w4) := 
              order3 u1 u2 u3 u4 in
              AllEdgesCompatible Coord3 GetSign
                GetIntersection w1 w2 w4 v3 w3 v1 v2 v3 v4
                u1 u2 u3 u4
        end
    end.
  Proof. Proof2.  Qed.

  Theorem Face4Compatible : 
    forall GetSign GetIntersection tid,
    match GetStructuredTet tid with
      ST v1 v2 v3 v4 _ _ _ (tid4, order4) =>
        match GetStructuredTet tid4 with 
          ST u1 u2 u3 u4 _ _ _ _ =>
            let '(w1, w2, w3, w4) := 
              order4 u1 u2 u3 u4 in
              AllEdgesCompatible Coord3 GetSign
                GetIntersection w1 w2 w3 v4 w4 v1 v2 v3 v4
                u1 u2 u3 u4
        end
    end.
  Proof. Proof2.  Qed.

End Structured_Unstructured_Proof.

