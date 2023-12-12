(* val reduce = fn : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a *)
fun reduce _ acc [] = acc 
|   reduce f acc (gl::rep)  = ((reduce f) ((f acc) gl)) rep

(* val squares = fn : int list -> int list *)
fun squares sez = (List.map (fn x => x*x)) sez   

(* val onlyEven = fn : int list -> int list *)
fun onlyEven sez = (List.filter (fn x => x mod 2 = 0)) sez

(* val bestString = fn : (string * string -> bool) -> string list -> string *)
fun bestString f sez = let fun compare(st1,st2) = if f(st1, st2) then st1 else st2 in
    ((List.foldl compare) "") sez 
    end

(* val largestString = fn : string list -> string *)
fun largestString  sez = bestString (fn (st1,st2) => st1 >= st2) sez



(* val largestString = fn : string list -> string *)
fun longestString sez = 
    let fun compSize(st1,st2) = String.size(st1) >= String.size(st2)
    in  (bestString compSize) sez
    end

(* val quicksort = fn : ('a * 'a -> order) -> 'a list -> 'a list *)
fun quicksort f (gl::rep) =
    let val (left, right) = List.partition (fn x => f (x, gl) = LESS) rep
    in (quicksort f left) @ (gl::(quicksort f right))
    end
|   quicksort _ [] = []

(* val dot = fn : int list -> int list -> int *)
fun dot sez1 sez2 = 
    let fun sum sez = List.foldl (op+) 0 sez 
    in sum(ListPair.map (fn (x,y) => x*y) (sez1,sez2))
    end


(* val transpose = fn : 'a list list -> 'a list list *)
fun transpose [] = []
|   transpose matrix = 
    let val max_n = List.length(hd matrix)
        fun get_row(n, sez as gl::rep) = List.nth(gl, n)::get_row(n, rep)
        |   get_row (_, _) = []
        fun transpose_r (n, matrix) = if n < max_n 
                                      then get_row(n, matrix) :: transpose_r(n+1,matrix)
                                      else []
    in
        transpose_r(0,matrix)
    end

(* val multiply = fn : int list list -> int list list -> int list list *)
fun multiply mx1 mx2 = 
    let fun get_row (row, gl::rep) = ((dot row) gl)::get_row(row,rep)
        |   get_row (_, []) = []
        fun multiply_r(gl::rep, mx2) = get_row(gl, mx2)::multiply_r(rep,mx2)
        |   multiply_r ([], _) = []
    in
        multiply_r(mx1,transpose mx2)
    end


fun group [] = []
|   group sez =
    let fun count_inc(el, acc as gl::_) = if (el = #1 gl) 
                                          then (el, (#2 gl) + 1)::acc 
                                          else (el, 1)::acc
        |   count_inc(el, []) = [(el, 1)]

        fun filter_repetitions(el as (el_k, _), acc as (acc_k, _)::_) = if el_k = acc_k 
                                                                then acc 
                                                                else el::acc
        |   filter_repetitions(el, []) = [el]

    in List.foldl filter_repetitions [] (List.foldl count_inc [] sez)
    end

(* val equivalenceClasses = fn : ('a -> 'a -> bool) -> 'a list -> 'a list list *)
fun equivalenceClasses _ [] = []
|   equivalenceClasses f sez = 
    let fun class_all_el (f, sez, gl::rep) = (List.filter (f gl) sez) :: class_all_el(f, sez, rep)
        |   class_all_el (_, _, []) = []
        fun exists(n, gl::rep) = if n = gl then true else exists(n, rep)
        |   exists(_, []) = false 
    in List.foldl (fn (el,acc) => if exists(el, acc) then acc else acc@[el]) [] (class_all_el(f, sez, sez))
    end
