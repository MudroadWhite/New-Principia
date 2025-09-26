Require Import Unicode.Utf8.
Require Import ClassicalFacts.
Require Import Classical_Prop.
Require Import PropExtensionality.

From Ltac2 Require Import Ltac2 Printf.

(* 
¬(P ∨ Q) → ¬P.
¬(P ∨ Q) → (¬P ∨ Q).
¬(P ∨ Q) → (P ∨ ¬Q).
¬(P ∨ Q) → (¬P ∨ ¬Q).
  ¬(P → Q) → (¬P → Q).
    ¬(P → Q) → (P → ¬Q).
*)

(* Ltac2 print_goals0 () :=
  Control.enter (fun () =>
  match! goal with
  [ |- ?t] => printf "the goal is %t" t
  end
  ).

Ltac2 Notation print_goals := print_goals0 ().

Ltac2 rec left_or_right () :=
  multi_match! goal with
  | [ |- _ \/ _ ] => print_goals; printf "use left"; left; left_or_right ()
  | [ |- _ \/ _ ] => print_goals; printf "use right"; right; left_or_right ()
  | [ |- ?t ] => printf "the final goal is %t" t ; printf "-------"
  end. *)

(* 
find_second_in_list (target : constr) (l : constr list) (count : int) :=
match l with
| [] => None
| hd :: tl =>
    match find_second_occurrence target hd count with
    | Some x => Some x
    | None => find_second_in_list target tl count
    end
end.
*)

(* Ltac2 rec simple_traversal (c : constr) :=
  print (of_string "traverse on");
  print (of_constr c);
  match (Constr.Unsafe.kind c) with
  | Constr.Unsafe.Var v =>
    print (of_string "Var");
    print (of_ident v)
  | Constr.Unsafe.App _ ca => 
    print (of_string "App");
    let ca := Array.to_list ca in
      Ltac2.List.iter (fun x => 
        simple_traversal x) ca
  | Constr.Unsafe.Constant _ _ => 
  (* let mca := Array.to_list (Array.map Message.of_constr ca) in *)
    print (of_string "Constant")
  | _ => print (of_string "unhandled")
  end
.  *)

(* Goal True.
assert (x : Prop). admit.
assert (P : Prop -> Prop). admit.
assert (h : P x \/ P x). admit.
assert (h1 : P x \/ P x \/ P x). admit.
(* Message.print (Message.of_constr 'h). *)
let h := Control.hyp ident:(h1) in 
let th := Constr.type h in
  print (of_string "simple traverse starts...");
  simple_traversal th
  (* print (of_string "traverse starts..."); *)
  (* match Constr.Unsafe.kind th with
  | Constr.Unsafe.App _ ca => 
  let mca := Array.to_list (Array.map Message.of_constr ca) in
    Ltac2.List.iter (fun x => print x) mca
  | _ => 
  print (of_string "not found")
  end *)
. 
Admitted. *)

(* let t := match hyp with
| (_, _, _) => hyp
end in
Message.print (Message.of_constr t). *)

  
(* Set Default Proof Mode "Classic". *)

(* Goal True.
  assert (x : Prop). admit.
  assert (P : Prop -> Prop). admit. 
  assert (h : P x \/ P x). admit.
  let hh := ltac2:(ident:(h)) in
  (* let hhh := ltac2:(ident_of_option hh) in *)
  idtac "test".
  match ltac2:(Ident.of_string "h") with
  | Some xx => ltac2:(show_term xx)
  | None => idtac "ltac2 failed"
  end. *)

(* TODO: write a function to test *)

(* 
NOTE: starting from *9, propositions are no longer just elementary(by p.144 of the pdf)
*)