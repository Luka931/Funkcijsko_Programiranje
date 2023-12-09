datatype natural = Succ of natural | One;
exception NotNaturalNumber;

datatype 'a bstree = br of 'a bstree * 'a * 'a bstree | lf;
datatype direction = L | R;


fun zip(xi::xr, yi::yr) = (xi,yi)::zip(xr,yr)
|   zip _ = []

fun unzip((xi, yi)::r) = 
    let val temp = unzip(r)
    in 
        (xi::(#1 temp),yi::(#2 temp))
    end
|   unzip _ = ([],[])

fun subtract (Succ(a), Succ(b)) = subtract(a,b)
|   subtract (Succ(a), One) = a
|   subtract (One, _) = raise NotNaturalNumber

fun any(f, g::r) = f(g) orelse any(f,r)
|   any _ = false 

fun map(f, g::r) = (f g) :: map(f,r)
|   map _ = []

fun filter (f, g::r) = 
    if(f g)
    then g::filter(f,r)
    else filter(f,r)
|   filter _ = []

fun fold(f, z, g::r) = 
    (case r of
        nil => f(z, g)
    |   _   => fold(f,f(z,g),r))
|   fold(_, z, nil) = z 

fun rotate(drevo as br(l, n, r), R  : direction) =
    (case l of
        br (l_l ,l_n, l_r) => br(l_l, l_n,br(l_r,n,r))
    |   lf => drevo)

|   rotate(drevo as br(l, n, r), L  : direction) = 
    (case r of
        br (r_l, r_n, r_r) => br(br(l, n, r_l), r_n, r_r)
    |   lf => drevo)

|   rotate(lf, _) = lf 

fun tree_height(br(left, _, right)) = 1 + Int.max(tree_height(left),tree_height(right))
|   tree_height _ = 1

fun BF(br(left, _, right)) = tree_height(left) - tree_height(right)
|   BF _ = 0

fun rebalance(drevo as br(left, i, right)) = 
    let val bf = BF(drevo)
    in
        if bf = 2
        then (if BF(left) >= 0
              then rotate(drevo,R)
              else rotate(br(rotate(left,L),i,right),R))
        else if bf = ~2
        then (if BF(right) <= 0
              then rotate(drevo,L)
              else rotate(br(left,i,rotate(right,R)),L))
        else drevo
    end
|   rebalance lf = lf

fun avl(c, drevo as br(left, i, right), e) =
    (case c(e,i) of 
        LESS => rebalance(br(avl(c, left, e),i,right))
    |   GREATER => rebalance(br(left, i, avl(c,right,e)))
    |   EQUAL => drevo)
|   avl(_, lf, e) = br(lf,e,lf) 