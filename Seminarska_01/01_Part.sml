val _ = Control.Print.printDepth := 10;
val _ = Control.Print.printLength := 10;
val _ = Control.Print.stringDepth := 2000;
val _ = Control.polyEqWarn := false;


fun readFile filename =
    let val is = TextIO.openIn filename
    in 
        String.map (fn c => if Char.isGraph c orelse c = #" " orelse c = #"\n" then c else #" ")
            (TextIO.inputAll is)
        before TextIO.closeIn is
    end

exception NotImplemented;

fun split n [] = []
|   split 0 _ = []
|   split n list = List.take(list,n)::(split n (List.drop(list,n)))
    handle Subscript => []

fun xGCD(0, b) = (b, 0, 1)
|   xGCD(a,b) = 
    let val (gcd, x1, y1) = xGCD(b mod a, a)
    in (gcd, y1 - (b div a) * x1, x1)
    end

signature RING =
sig
    eqtype t
    val zero : t
    val one : t
    val neg : t -> t
    val xGCD : t * t -> t * t * t
    val inv : t -> t option
    val + : t * t -> t
    val * : t * t -> t
end;

functor Ring (val n : int) :> RING where type t = int =
struct
    type t = int
    val zero = 0
    val one = 1
    fun neg x = ~x mod n
    val xGCD = xGCD
    
    fun inv x =
        case xGCD (x mod n, n) of
            (1, s, _) => SOME (s mod n)
        | _ => NONE

    fun op + a = Int.+ a mod n
    fun op * p = Int.* p mod n
end;

signature MAT =
sig
    eqtype t
    structure Vec :
        sig
            val dot : t list -> t list -> t
            val add : t list -> t list -> t list
            val sub : t list -> t list -> t list
            val scale : t -> t list -> t list
        end
    val tr : t list list -> t list list
    val mul : t list list -> t list list -> t list list
    val id : int -> t list list
    val join : t list list -> t list list -> t list list
    val inv : t list list -> t list list option
end;

functor Mat (R : RING) :> MAT where type t = R.t =
struct
    type t = R.t
    structure Vec =
        struct
            fun dot vec1 vec2 = List.foldl R.+ R.zero (ListPair.map R.* (vec1, vec2))
            fun add seq1 seq2= ListPair.map R.+ (seq1, seq2)
            fun sub seq1 seq2 = ListPair.map (fn (x,y) => R.+(x, R.neg(y))) (seq1, seq2)
            fun scale n seq = List.map (fn x => R.*(x, n)) seq

        end
    fun tr [] = []
    |   tr matrix =     
        let fun getRow matrix n = List.map (fn x => List.nth(x,n)) matrix 
        in List.tabulate(List.length (hd matrix), (getRow matrix)) handle Subscript => [[]]
        end

    fun mul mx1 mx2 = let fun get_row (row, mx2) = List.map (fn x => Vec.dot row x) mx2
                          fun multiply_r(mx1, mx2) = List.map (fn x => get_row(x,mx2)) mx1
                      in multiply_r(mx1,tr mx2)
                      end

    fun id n = let fun getElement(x,y) = if x = y then R.one else R.zero
               in split n (List.map getElement (List.tabulate(n*n, fn x => (x div n, x mod n)))) 
               end

    fun join [] mx2 = mx2
    |   join mx1 [] = mx1
    |   join mx1 mx2 = ListPair.map List.@ (mx1, mx2)


    fun inv matrix = 
    let 
        fun reduce v m = List.map (fn x :: u => Vec.sub u (Vec.scale x v) | _ => raise Empty) m

        fun pivot ((v as x :: _ ):: m) = 
            (case R.inv x of 
                SOME x' => SOME (Vec.scale x' v :: m)
            |   NONE => case m of
                    ((u as y :: _) :: m') => let val (g, s, t) = R.xGCD (x, y) in
                                case pivot (Vec.add (Vec.scale s v) (Vec.scale t u) :: m') of
                                    SOME (w :: m'') => SOME (w :: u :: v :: m'')
                                |   _ => NONE
                                end
            |    _ => NONE)
        |   pivot _ = NONE

        fun gauss (above, []) = SOME above
        |   gauss (above, below) = case pivot below of 
                SOME ((_ :: v) :: m) => gauss (reduce v above @ [v], List.filter (List.exists (fn x => x <> R.zero)) (reduce v m)) 
            |    _ => NONE
    in 
        gauss([], join matrix (id (List.length matrix)))
    end

end;

signature CIPHER =
sig
    type t
    val encrypt : t list list -> t list -> t list
    val decrypt : t list list -> t list -> t list option
    val knownPlaintextAttack : int -> t list -> t list -> t list list option
end;

functor HillCipherAnalyzer (M : MAT) :> CIPHER
    where type t = M.t
=
struct
    type t = M.t
    
    fun encrypt key plainText = let val n = List.length key
                                in List.concat(List.concat (List.map (fn x => M.mul [x] key) (split n plainText)))
                                end 
    fun decrypt key cipherText = case M.inv key of
                                    SOME invKey => SOME(encrypt invKey cipherText)
                                 |  NONE => NONE
    
    fun knownPlaintextAttack keyLenght plainText cipherText = 
        let fun checkValidity matrix plainText cipherText = (encrypt matrix plainText) = cipherText
            val plainTextSplit = split keyLenght plainText
            val ciphertextSplit = split keyLenght cipherText
            fun helperKPA t keyLenght plainText cipherText = 
            let val xCurr = List.take(plainTextSplit, t) handle Subscript => []
                val yCurr = List.take(ciphertextSplit, t) handle Subscript => []
            in  case (xCurr, yCurr, M.inv(M.mul (M.tr xCurr) xCurr)) of
                    ((_, [], _) | ([], _, _)) => let val newPlainText = List.drop(plainText, keyLenght) handle Subscript => []
                                                     val newCipherText = List.drop(cipherText, keyLenght) handle Subscript => []
                                                 in  knownPlaintextAttack keyLenght newPlainText newCipherText
                                                 end 
                |   (xCurr, yCurr, NONE) => helperKPA (t+1) keyLenght plainText cipherText
                |   (xCurr, yCurr, SOME xxInv) => let val newKey = M.mul  (M.mul xxInv (M.tr xCurr)) yCurr
                                                  in if checkValidity newKey plainText cipherText 
                                                     then SOME newKey 
                                                     else helperKPA (t+1) keyLenght plainText cipherText
                                                  end
            end
            val x = List.take(plainTextSplit, keyLenght) handle Subscript => []
            val y = List.take(ciphertextSplit, keyLenght) handle Subscript => []
        in
            case (x, y, M.inv(x)) of
                ((_, [], _) | ([], _, _)) => NONE
            |   (x, y, NONE) => helperKPA (keyLenght+1) keyLenght plainText cipherText
            |   (x, y, SOME xInv) => let val newKey = M.mul xInv y
                                     in if checkValidity newKey plainText cipherText 
                                        then SOME newKey 
                                        else helperKPA (keyLenght+1) keyLenght plainText cipherText
                                     end
        end
end;


structure Trie :>
sig
eqtype ''a dict
val empty : ''a dict
val insert : ''a list -> ''a dict -> ''a dict
val lookup : ''a list -> ''a dict -> bool
end
=
struct
    datatype ''a tree = N of ''a * bool * ''a tree list
    type ''a dict = ''a tree list

    val empty = [] : ''a dict


    fun insert (charSeq as chrGl::[]) ((dictGl as N(dictChr, isEnd, dictTree))::dictRep) = 
            if chrGl = dictChr
            then N(dictChr, true, dictTree)::dictRep
            else dictGl::(insert charSeq dictRep)
    |   insert (charSeq as chrGl::chrRep) ((dictGl as N(dictChr, isEnd, dictTree))::dictRep) =
            if chrGl = dictChr
            then N(dictChr, isEnd, insert chrRep dictTree)::dictRep
            else dictGl::(insert charSeq dictRep)
    |   insert (chrGl::[]) [] = [N(chrGl, true, empty)]
    |   insert (chrGl::chrRep) [] = [N(chrGl, false, insert chrRep empty)]

    fun lookup (charSeq as chrGl::[]) (N(dictChr, isEnd, _)::dictRep) = 
            if chrGl = dictChr andalso isEnd
            then true 
            else lookup charSeq dictRep
    |   lookup (charSeq as chrGl::chrRep) (N(dictChr, _, dictTree)::dictRep) = 
            if chrGl = dictChr
            then lookup chrRep dictTree
            else lookup charSeq dictRep
    |   lookup _ [] = false 
    |   lookup [] _ = false
end;

signature HILLCIPHER =
sig
    structure Ring : RING where type t = int
    structure Matrix : MAT where type t = Ring.t
    structure Cipher : CIPHER where type t = Matrix.t
    val alphabetSize : int
    val alphabet : char list
    val encode : string -> Cipher.t list
    val decode : Cipher.t list -> string
    val encrypt : Cipher.t list list -> string -> string
    val decrypt : Cipher.t list list -> string -> string option
    val knownPlaintextAttack :
            int -> string -> string -> Cipher.t list list option
    val ciphertextOnlyAttack : int -> string -> Cipher.t list list option
end

functor HillCipher (val alphabet : string) :> HILLCIPHER =
struct

(*printable characters*)
val alphabetSize = String.size alphabet
val alphabet = String.explode alphabet

structure Ring = Ring (val n = alphabetSize)
structure Matrix = Mat (Ring)
structure Cipher = HillCipherAnalyzer (Matrix)

fun encode txt = let val alphabetEnum = ListPair.zip(alphabet, List.tabulate(List.length alphabet, fn x => x))
                     fun codeChr ((currChr, currCode)::rep) chr = if currChr = chr then currCode else (codeChr rep chr)
                     |   codeChr [] _ = raise NotImplemented
                 in List.map (codeChr alphabetEnum) (String.explode txt)
                 end

fun decode code = let val alphabetEnum = ListPair.zip(alphabet, List.tabulate(List.length(alphabet), fn x => x))
                      fun codeToChr ((currChr, currCode)::rep) code = if currCode = code then currChr else (codeToChr rep code)
                      |   codeToChr [] _ = raise NotImplemented
                  in String.implode  (List.map (codeToChr alphabetEnum) code)
                  end

local
    fun parseWords filename =
        let val is = TextIO.openIn filename
            fun read_lines is =
                case TextIO.inputLine is of
                    SOME line =>
                        if String.size line > 1
                        then String.tokens (not o Char.isAlpha) line @ read_lines is
                        else read_lines is
                    | NONE => []
        in List.map (String.map Char.toLower) (read_lines is) before TextIO.closeIn is end

    val dictionary = List.foldl (fn (w, d) => Trie.insert w d) Trie.empty (List.map String.explode (parseWords "hamlet.txt")) handle NotImplemented => Trie.empty
in
    fun encrypt key plainText = decode (Cipher.encrypt key (encode plainText))
    fun decrypt key cipherText = case (Cipher.decrypt key (encode cipherText)) of 
                                    SOME plainText => SOME (decode plainText)
                                 |  NONE => NONE
    fun knownPlaintextAttack keyLenght plainText cipherText = Cipher.knownPlaintextAttack keyLenght (encode plainText) (encode cipherText)

    fun ciphertextOnlyAttack keyLenght cipherText =
    let val startMatrix = List.tabulate(keyLenght, fn _ => List.tabulate(keyLenght, fn _ => 0))
        fun getElement (matrix, row, col) = List.nth((List.nth(matrix,row)),col)
        fun applyToNth (seq, f, n) = List.take(seq,n)@((f (List.nth(seq,n)))::(List.drop(seq,n+1))) handle Subscript => seq
        fun incrementElement matrix pos = 
            let val n = List.length matrix
                val row = pos div n
                val col = pos mod n
                val newMatrix = applyToNth(matrix, fn rowSeq => applyToNth(rowSeq, fn el => (el+1) mod alphabetSize, col), row)
            in  if (getElement(matrix, row, col) + 1) mod alphabetSize = 0 andalso pos > 0
                then incrementElement newMatrix (pos-1)
                else newMatrix
            end
        fun getNextMatrix matrix = 
            let val n = List.length matrix
            in incrementElement matrix (n*n-1)
            end
        fun countWords(key, cipherText) = 
            case decrypt key cipherText of
                SOME text => List.foldl (Int.+) 0 (List.map (fn word => if Trie.lookup (String.explode word) dictionary then 1 else 0) (String.tokens Char.isSpace text))
            |   NONE => ~1
        fun findBestKey cipherText currKey bestKey noWords = 
            let val newKey = getNextMatrix currKey
                val currWordCount = case Matrix.inv(currKey) of SOME _ => countWords(currKey, cipherText) | NONE => ~1
            in  if newKey = startMatrix
                then bestKey 
                else if currWordCount > noWords
                then findBestKey cipherText newKey currKey currWordCount
                else findBestKey cipherText newKey bestKey noWords
            end
    in  
        case findBestKey cipherText (getNextMatrix(startMatrix)) [[]] 0 of
            [[]] => NONE
        |   result => SOME(result) 
    end

    end
end;
