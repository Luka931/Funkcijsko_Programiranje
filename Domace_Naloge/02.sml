datatype number = Zero | Succ of number | Pred of number;

fun simp_r(Succ(Pred(a)) : number) : number = simp_r(a)
    |simp_r(Pred(Succ(a)) : number) = simp_r(a)
    |simp_r(Succ(a) : number) = Succ(simp_r(a))
    |simp_r(Pred(a):number) = Pred(simp_r(a))
    |simp_r(Zero : number) = Zero

fun simp(a : number) : number = 
    let val new = simp_r a
    in 
        if a = new 
        then new
        else simp(new)
    end


(* Negira število a. Pretvorba v int ni dovoljena! *)
fun neg (a : number) : number = 
    case a of
        Zero => Zero
    |   Succ a => Pred (neg a)
    |   Pred a => Succ (neg a)

(* Vrne vsoto števil a in b. Pretvorba v int ni dovoljena! *)
fun add (a : number, b : number) : number = 
    case b of
        Zero => a
    |   Succ k => add(Succ(a),k)
    |   Pred k => add(Pred(a),k)

(* Vrne rezultat primerjave števil a in b. Pretvorba v int ter uporaba funkcij `add` in `neg` ni dovoljena!
    namig: uporabi funkcijo simp *)
fun comp_r(Succ(a) : number, Succ(b):number) : order = comp_r(a,b)
    |comp_r(Succ _, Pred _) = GREATER
    |comp_r(Pred _, Succ _) = LESS
    |comp_r(Pred(a), Pred(b)) = comp_r(a,b)
    |comp_r(Succ _,Zero) = GREATER
    |comp_r(Zero, Pred _) = GREATER
    |comp_r(Pred _,Zero) = LESS
    |comp_r(Zero, Succ _) = LESS
    |comp_r(Zero,Zero) = EQUAL

fun comp (a : number, b : number) : order  = comp_r(simp(a),simp(b))
    

datatype tree = Node of int * tree * tree | Leaf of int;

(* Vrne true, če drevo vsebuje element x. *)
fun contains (Node (i,left,right) : tree, x : int) : bool = 
        (i = x) orelse contains(left,x) orelse contains(right,x)
|   contains(Leaf i : tree, x : int) = (i = x)

(* Vrne število listov v drevesu. *)
fun countLeaves (Leaf _ : tree) : int = 1
|   countLeaves(Node (_,left,right) : tree) = countLeaves(left) + countLeaves(right)

(* Vrne število število vej v drevesu. *)
fun countBranches (Node (_,left,right) : tree) : int = 
        2 + countBranches(left) + countBranches(right)
|   countBranches _ = 0

(* Vrne višino drevesa. Višina lista je 1. *)
fun height (Node (_,left,right) : tree) : int = 1 + Int.max(height(left),height(right))
|   height(Leaf _) = 1
        

(* Pretvori drevo v seznam z vmesnim prehodom (in-order traversal). *)
fun join(g::r : int list, b : int list) : int list = g::join(r,b)
|   join(_, b) = b

fun toList (Node (i,left,right) : tree) : int list = 
    join(toList(left),i::toList(right))
|   toList(Leaf i : tree) = i::nil 


(* Vrne true, če je drevo uravnoteženo:
 * - Obe poddrevesi sta uravnoteženi.
 * - Višini poddreves se razlikujeta kvečjemu za 1.
 * - Listi so uravnoteženi po definiciji.
 *)

fun isBalanced (Node(_,left,right) : tree) : bool =
        isBalanced(left) andalso isBalanced(right) andalso Int.abs(height(left) - height(right)) <= 1
|   isBalanced(Leaf _) = true

(* Vrne true, če je drevo binarno iskalno drevo:
 * - Vrednosti levega poddrevesa so strogo manjši od vrednosti vozlišča.
 * - Vrednosti desnega poddrevesa so strogo večji od vrednosti vozlišča.
 * - Obe poddrevesi sta binarni iskalni drevesi.
 * - Listi so binarna iskalna drevesa po definiciji.
 *)
fun min(Node(i, left, right) : tree) : int = Int.min(i,Int.min(min(left),min(right)))
|   min(Leaf i : tree) : int = i

fun max(Node(i, left, right) : tree) : int = Int.max(i,Int.max(max(left),max(right)))
|   max(Leaf i : tree) : int = i

fun isBST (Node(i,left,right) : tree) : bool = 
       isBST(left) andalso isBST(right) andalso i > max(left) andalso i < min(right)
|   isBST(Leaf _) = true