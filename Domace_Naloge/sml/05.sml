structure Rational  =
struct
    datatype rational = whole of int | fraction of int * int
  
    exception BadRational

    fun GCD (a, 0) = a
    |   GCD (a, b) = if Int.abs(a) > Int.abs(b)
                     then GCD (b, a mod b) 
                     else GCD (a, b mod a)

    fun makeRational (_, 0) = raise BadRational
    |   makeRational (0, _) = whole 0
    |   makeRational (a, b) = let val bSign = Int.sign(b)
                                  val aSign = Int.sign(a)
                                  val aAbs = Int.abs(a)
                                  val bAbs = Int.abs(b)
                                  val gcd = GCD(aAbs,bAbs)
                              in if gcd = bAbs
                                 then whole ((aAbs div gcd) * bSign * aSign)  
                                 else fraction((aAbs div gcd)*bSign*aSign, (bAbs div gcd))
                              end

    fun neg (whole a) = makeRational(a * ~1,1)
    |   neg (fraction (a, b))  = makeRational(a, ~1 * b)

    fun inv (whole a) = makeRational(1, a)
    |   inv (fraction (a,b)) = makeRational(b,a)

    fun add(whole a, whole b) = makeRational(a+b, 1)
    |   add(fraction (a1, a2), whole b) = makeRational(a1 + a2*b, a2)
    |   add(whole a, fraction (b1, b2)) = makeRational(b1 + b2*a, b2)
    |   add(fraction(a1, a2), fraction (b1, b2)) = makeRational(a1*b2 + b1*a2, a2*b2)

    
    fun mul(whole a, whole b) = makeRational(a*b, 1)
    |   mul(fraction (a1, a2), whole b) = makeRational(a1*b, a2)
    |   mul(whole a, fraction (b1, b2)) = makeRational(b1*a, b2)
    |   mul(fraction(a1, a2), fraction (b1, b2)) = makeRational(a1*b1, a2*b2)

    fun toString(whole a) = Int.toString(a)
    |   toString(fraction (a,b)) = Int.toString(a) ^ "/" ^ Int.toString(b)

end

signature EQ =
sig
    type t
    val eq : t -> t -> bool
end

signature SET =
sig
    (* podatkovni tip za elemente množice *)
    type item

    (* podatkovni tip množico *)
    type set

    (* prazna množica *)
    val empty : set

    (* vrne množico s samo podanim elementom *)
    val singleton : item -> set

    (* unija množic *)
    val union : set -> set -> set

    (* razlika množic (prva - druga) *)
    val difference : set -> set -> set

    (* a je prva množica podmnožica druge *)
    val subset : set -> set -> bool
end

functor SetFn (Eq : EQ) :> SET where type item = Eq.t =
struct
    type item = Eq.t
    type set = item list
    val empty : set = []

    fun singleton x = x :: []
    fun union x y = let fun unionR (gl::rep, acc) = unionR(List.filter (fn x => not (Eq.eq x gl)) rep, acc@[gl])
                        |   unionR ([], acc) = acc
                    in unionR (x@y, [])
                    end
    fun difference x y = let val xFiltered = List.filter  (fn xEl => List.exists (fn yEl => Eq.eq xEl yEl) y) x
                             val yFiltered = List.filter  (fn yEl => List.exists (fn xEl => Eq.eq yEl xEl) x) y
                        in union xFiltered yFiltered
                        end

    fun subset nil _ = true
    |   subset (gl::rp) y = List.exists (fn yEl => Eq.eq gl yEl) y andalso subset rp y
end;


funsig SETFN (Eq : EQ) = SET
