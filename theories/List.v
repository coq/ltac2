(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Int.
Require Ltac2.Control.
Require Ltac2.Bool.

Ltac2 rec length (ls : 'a list) :=
  match ls with
  | [] => 0
  | _ :: xs => Int.add 1 (length xs)
  end.
Ltac2 cons (x : 'a) (xs : 'a list) :=
  x :: xs.
Ltac2 hd_error (ls : 'a list) :=
  match ls with
  | [] => None
  | x :: xs => Some x
  end.
Ltac2 hd_default (default : 'a) (ls : 'a list) :=
  match hd_error ls with
  | Some v => v
  | None => default
  end.
Ltac2 hd (ls : 'a list) :=
  match ls with
  | [] => Control.zero (Tactic_failure None)
  | x :: xs => x
  end.
Ltac2 tl (ls : 'a list) :=
  match ls with
  | [] => []
  | x :: xs => xs
  end.
Ltac2 rec nth_error_aux (ls : 'a list) (n : int) :=
  match ls with
  | [] => None
  | x :: xs
    => match Int.equal n 0 with
       | true => Some x
       | false => nth_error_aux xs (Int.sub n 1)
       end
  end.
Ltac2 nth_error (ls : 'a list) (n : int) :=
  match Int.equal (Int.compare n 0) -1 with
  | true => Control.zero (Tactic_failure None)
  | false => nth_error_aux ls n
  end.
Ltac2 nth_default (default : 'a) (ls : 'a list) (n : int) :=
  match nth_error ls n with
  | Some v => v
  | None => default
  end.
Ltac2 nth (ls : 'a list) (n : int) :=
  match nth_error ls n with
  | Some v => v
  | None => Control.zero Out_of_bounds
  end.
Ltac2 rec rev_append (l1 : 'a list) (l2 : 'a list) :=
  match l1 with
  | [] => l2
  | a :: l => rev_append l (a :: l2)
  end.
Ltac2 rev l := rev_append l [].
Ltac2 rec append ls1 ls2 :=
  match ls1 with
  | [] => ls2
  | x :: xs => x :: append xs ls2
  end.
Ltac2 app ls1 ls2 := append ls1 ls2.
Ltac2 rec flatten (ls : 'a list list) :=
  match ls with
  | [] => []
  | x :: xs => app x (flatten xs)
  end.
Ltac2 concat (ls : 'a list list) := flatten ls.
Ltac2 rec iter (f : 'a -> unit) (ls : 'a list) :=
  match ls with
  | [] => ()
  | l :: ls => f l; iter f ls
  end.
Ltac2 rec iteri_aux (i : int) (f : int -> 'a -> unit) (ls : 'a list) :=
  match ls with
  | [] => ()
  | l :: ls => f i l; iteri_aux (Int.add i 1) f ls
  end.
Ltac2 iteri (f : int -> 'a -> unit) (ls : 'a list) :=
  iteri_aux 0 f ls.
Ltac2 rec map (f : 'a -> 'b) (ls : 'a list) :=
  match ls with
  | [] => []
  | l :: ls => f l :: map f ls
  end.
Ltac2 rec mapi_aux (i : int) (f : int -> 'a -> 'b) (ls : 'a list) :=
  match ls with
  | [] => []
  | l :: ls => f i l :: mapi_aux (Int.add i 1) f ls
  end.
Ltac2 mapi (f : int -> 'a -> 'b) (ls : 'a list) :=
  mapi_aux 0 f ls.
(* from the OCaml std lib *)
Ltac2 rec rev_map (f : 'a -> 'b) (ls : 'a list) :=
  let rec rmap_f accu ls :=
      match ls with
      | [] => accu
      | a::l => rmap_f (f a :: accu) l
      end in
  rmap_f [] ls.
Ltac2 rec fold_right (f : 'a -> 'b -> 'b) (a : 'b) (ls : 'a list) :=
  match ls with
  | [] => a
  | l :: ls => f l (fold_right f a ls)
  end.
Ltac2 rec fold_left (f : 'a -> 'b -> 'a) (xs : 'b list) (a : 'a) :=
  match xs with
  | [] => a
  | x :: xs => fold_left f xs (f a x)
  end.
Ltac2 rec all f ls :=
  match ls with
  | [] => true
  | x :: xs => match f x with
               | true => all f xs
               | false => false
               end
  end.
Ltac2 rec any f ls :=
  match ls with
  | [] => false
  | x :: xs => match f x with
               | true => true
               | false => any f xs
               end
  end.
Ltac2 rec find_error f xs :=
  match xs with
  | [] => None
  | x :: xs => match f x with
               | true => Some x
               | false => find_error f xs
               end
  end.
Ltac2 rec find f xs :=
  match find_error f xs with
  | Some v => v
  | None => Control.zero Not_found
  end.
Ltac2 rec find_rev_error f xs :=
  match xs with
  | [] => None
  | x :: xs => match find_rev_error f xs with
               | Some v => Some v
               | None => match f x with
                         | true => Some x
                         | false => None
                         end
               end
  end.
Ltac2 find_rev f xs :=
  match find_rev_error f xs with
  | Some v => v
  | None => Control.zero Not_found
  end.
Ltac2 rec filter f xs :=
  match xs with
  | [] => []
  | x :: xs
    => match f x with
       | true => x :: filter f xs
       | false => filter f xs
       end
  end.
Ltac2 rec filter_out f xs :=
  filter (fun x => Bool.negb (f x)) xs.
Ltac2 rec iter2 f xs ys :=
  match xs with
  | []
    => match ys with
       | [] => ()
       | _ :: _ => Control.zero (Tactic_failure None)
       end
  | x :: xs
    => match ys with
       | [] => Control.zero (Tactic_failure None)
       | y :: ys
         => f x y; iter2 f xs ys
       end
  end.
Ltac2 rec map2 (f : 'a -> 'b -> 'c) (xs : 'a list) (ys : 'b list) :=
  match xs with
  | []
    => match ys with
       | [] => []
       | _ :: _ => Control.zero (Tactic_failure None)
       end
  | x :: xs
    => match ys with
       | [] => Control.zero (Tactic_failure None)
       | y :: ys
         => f x y :: map2 f xs ys
       end
  end.
Ltac2 rec fold_right2 (f : 'a -> 'b -> 'c -> 'c) (a : 'c) (xs : 'a list) (ys : 'b list) :=
  match xs with
  | []
    => match ys with
       | [] => a
       | _ :: _ => Control.zero (Tactic_failure None)
       end
  | x :: xs
    => match ys with
       | [] => Control.zero (Tactic_failure None)
       | y :: ys
         => f x y (fold_right2 f a xs ys)
       end
  end.
Ltac2 rec fold_left2 (f : 'a -> 'b -> 'c -> 'a) (xs : 'b list) (ys : 'c list) (a : 'a) :=
  match xs with
  | []
    => match ys with
       | [] => a
       | _ :: _ => Control.zero (Tactic_failure None)
       end
  | x :: xs
    => match ys with
       | [] => Control.zero (Tactic_failure None)
       | y :: ys
         => fold_left2 f xs ys (f a x y)
       end
  end.
Ltac2 rec all2_aux f f_x f_y xs ys :=
  match xs with
  | [] => all f_y ys
  | x :: xs'
    => match ys with
       | [] => all f_x xs
       | y :: ys'
         => match f x y with
            | true => all2_aux f f_x f_y xs' ys'
            | false => false
            end
       end
  end.
Ltac2 all2 f xs ys :=
  let on_different_lengths () :=
      Control.zero (Tactic_failure None) in
  all2_aux
    f (fun _ => on_different_lengths ()) (fun _ => on_different_lengths ())
    xs ys.
Ltac2 rec any2_aux f f_x f_y xs ys :=
  match xs with
  | [] => any f_y ys
  | x :: xs'
    => match ys with
       | [] => any f_x xs
       | y :: ys'
         => match f x y with
            | true => true
            | false => any2_aux f f_x f_y xs' ys'
            end
       end
  end.
Ltac2 any2 f xs ys :=
  let on_different_lengths () :=
      Control.zero (Tactic_failure None) in
  any2_aux
    f (fun _ => on_different_lengths ()) (fun _ => on_different_lengths ())
    xs ys.
Ltac2 rec combine (ls1 : 'a list) (ls2 : 'b list) :=
  match ls1 with
  | []
    => match ls2 with
       | [] => []
       | _ :: _ => Control.zero (Tactic_failure None)
       end
  | x :: xs
    => match ls2 with
       | y :: ys
         => (x, y) :: combine xs ys
       | [] => Control.zero (Tactic_failure None)
       end
  end.
Ltac2 rec split (ls : ('a * 'b) list) :=
  match ls with
  | [] => ([], [])
  | l :: ls
    => let ((x, y)) := l in
       let ((xs, ys)) := split ls in
       ((x::xs), (y::ys))
  end.

Ltac2 rec seq (start : int) (step : int) (last : int) :=
  match Int.equal (Int.compare (Int.sub last start) step) -1 with
  | true
    => []
  | false
    => start :: seq (Int.add start step) step last
  end.
Ltac2 enumerate (ls : 'a list) :=
  combine (seq 0 1 (length ls)) ls.
