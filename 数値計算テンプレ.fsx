open System
open System.Collections
open System.Collections.Generic
open System.Linq
open System.IO
open System.Text
open System.Numerics
open System.Diagnostics
open System.Runtime.InteropServices
open System.Runtime.CompilerServices



// 総乗
let inline product xs =
    Seq.fold (*) LanguagePrimitives.GenericOne xs
// 二項mod積
let inline productModBinomal m a b =
    a * b % m
// mod総乗
//依存 : 二項mod積
let inline productMod m xs =
    let one = LanguagePrimitives.GenericOne
    Seq.fold (productModBinomal m) (one % m) xs

// 累乗計算 O(log p)
let inline pow (a: ^a) (p: ^p) : ^a =
    let zero = LanguagePrimitives.GenericZero
    let one = LanguagePrimitives.GenericOne
    let two = one + one

    let rec loop baseValue exp acc =
        if exp = zero then
            acc
        elif exp % two = one then
            loop (baseValue * baseValue) (exp / two) (acc * baseValue)
        else
            loop (baseValue * baseValue) (exp / two) acc

    if p < zero then
        failwith "負の指数はサポートされていません"
    else
        loop a p one

// 乗算方法と単位元を差し替え可能なmod累乗
let inline modpowBy mulMod one m a p =
    let zero = LanguagePrimitives.GenericZero
    let oneExp = LanguagePrimitives.GenericOne
    let two = oneExp + oneExp

    let rec loop baseValue exp acc =
        if exp = zero then
            acc % m
        elif exp % two = oneExp then
            loop (mulMod m baseValue baseValue) (exp / two) (mulMod m acc baseValue)
        else
            loop (mulMod m baseValue baseValue) (exp / two) acc
    
    if p < zero then
        failwith "負の指数はサポートされていません"
    else
        loop (a % m) p one

// 通常の二項mod積によるmod累乗
let inline modpow m a p =
    let one = LanguagePrimitives.GenericOne
    modpowBy productModBinomal one m a p


// UInt128を使ったMontgomery乗算（法は2以上の奇数）。
// R = 2^64 とし、値はMontgomery領域にあるものとする。
type MontgomeryContext =
    {
        Modulus: uint64
        MPrime: uint64
    }

let private montgomeryMPrime (m: uint64) =
    // m * inverse = 1 (mod 2^64) をNewton法で求める。
    let mutable inverse = 1UL
    for _ in 1 .. 6 do
        inverse <- inverse * (2UL - m * inverse)
    0UL - inverse

let createMontgomeryContext (m: uint64) =
    if m < 3UL || m % 2UL = 0UL then
        invalidArg "m" "Montgomery法の法は3以上の奇数である必要があります"

    {
        Modulus = m
        MPrime = montgomeryMPrime m
    }

let montgomeryReduce (context: MontgomeryContext) (t: UInt128) =
    let m = UInt128.CreateChecked context.Modulus
    let q =
        UInt128.CreateChecked (
            uint64 (
                UInt128.CreateChecked (uint64 t)
                * UInt128.CreateChecked context.MPrime
            )
        )
    let sum = t + q * m
    let carry =
        if sum < t then UInt128.CreateChecked 1UL
        else UInt128.CreateChecked 0UL
    let u = (sum >>> 64) + (carry <<< 64)

    if u >= m then
        uint64 (u - m)
    else
        uint64 u

let montgomeryMul (context: MontgomeryContext) (a: uint64) (b: uint64) =
    montgomeryReduce context (UInt128.CreateChecked a * UInt128.CreateChecked b)

let montgomeryTo (context: MontgomeryContext) (a: uint64) =
    let m = UInt128.CreateChecked context.Modulus
    uint64 ((UInt128.CreateChecked a <<< 64) % m)

let montgomeryFrom (context: MontgomeryContext) (a: uint64) =
    montgomeryReduce context (UInt128.CreateChecked a)

let montgomeryPow (m: uint64) (a: uint64) (p: uint64) =
    let context = createMontgomeryContext m
    let one = montgomeryTo context 1UL
    let value = montgomeryTo context (a % m)

    let product _ x y = montgomeryMul context x y
    let result = modpowBy product one m value p
    montgomeryFrom context result

// Montgomeryここまで

// MillerRabin素数判定
// 依存 : Montgomery乗算
// true -> 素数
let inline MillerRabin (n: int64) =
    let tester =
        if n < 4759123141L then
            [|2L; 7L; 61L|]
        else
            [|2L; 325L; 9375L; 28178L; 450775L; 9780504L; 1795265022L|]

    // 自明解を先に消す
    if n < 2L then false
    elif n = 2L then true
    elif n % 2L = 0L then false
    else
        let s = BitOperations.TrailingZeroCount (n - 1L)
        let d = (n - 1L) / (1L <<< s)

        // 1回のテスト
        // a に対して、
        /// a^d ~= 1
        /// a^d ~= -1
        /// a^(2d) ~= -1
        /// a^(4d) ~= -1
        /// ...
        /// a^(2^(s-1)) ~= -1
        // がすべて偽であれば合成数 : false
        let Test a =
            let first = montgomeryPow (uint64 n) (uint64 a) (uint64 d)
            if first = 1UL || first = uint64 (n - 1L) then
                true
            else
                // いま now = a^(d * 2 ^ (pownum - 1)) まで検証
                let rec looptest now pownum =
                    if pownum >= s then false
                    else
                        let next = montgomeryPow (uint64 n) now 2UL
                        if next = uint64 (n - 1L) then true
                        else looptest next (pownum + 1)
                
                looptest first 1
        
        // i - 1 番目まで検証済み
        let rec testLoop i =
            if i >= tester.Length then
                true
            elif tester.[i] >= n then
                testLoop (i + 1)
            elif Test tester.[i] then
                testLoop (i + 1)
            else
                false

        testLoop 0

// MillerRabin ここまで



// 最大公約数
let inline gcd a b =
    let rec gcds a b =
        if b = LanguagePrimitives.GenericZero then a
        else gcds b (a % b)
    gcds (abs a) (abs b)

// 拡張ユークリッド互除法
// g = a * x + b * y
let ext_gcd a b =
    let zero = LanguagePrimitives.GenericZero
    let one = LanguagePrimitives.GenericOne
    let rec calc a b cont =
        if b = zero then
            cont a one zero
        else
            let next_cont g x1 y1 = cont g y1 (x1 - a / b * y1) in
            calc b (a % b) next_cont in
    calc a b (fun g x y -> g, x, y)


// 整数型平方根 O(log n)
let inline isqrt (n: ^T) : ^T =
    let zero = LanguagePrimitives.GenericZero<^T>
    let one = LanguagePrimitives.GenericOne<^T>
    let two = one + one

    if n < zero then 
        failwith "負の数は未定義です"
    elif n < two then 
        n
    else
        let rec binarySearch low high =
            if low > high then 
                high
            else
                let mid = low + (high - low) / two
                // mid * mid がオーバーフローするのを防ぐため、除算で判定
                if mid <= n / mid then
                    binarySearch (mid + one) high
                else
                    binarySearch low (mid - one)
        binarySearch one (n / two)


// エラトステネスの篩 O(N Log Log N)
// 依存 : isqrt
let PrimesUpTo (n: int) =
    let a = Array.init (n + 1) (fun _ -> true)
    a.[0] <- false
    a.[1] <- false
    for i in 2 .. (isqrt n) do
        if a.[i] then
            for j in 2*i .. i .. n do
                a.[j] <- false
    a
    |> Seq.mapi (fun i b -> if b then Some i else None)
    |> Seq.choose id
    |> Seq.toArray

// オイラーのファイ関数 
let inline EulerPhiWithPrimes (PrimeArray: ^I array) (n: ^I) =
    let zero = LanguagePrimitives.GenericZero
    PrimeArray
    |> Seq.choose (fun p ->
        if n % p = zero then Some p else None
    )
    |> Seq.fold (fun acc p -> acc - acc / p) n

// オイラーのファイ関数(単独)
// 依存 : EulerPhiWithPrimes, PrimesUpTo, isqrt
let inline EulerPhi n =
    EulerPhiWithPrimes (PrimesUpTo(n: int)) n

// mod逆数
// 依存 : EulerPhiWithPrimes, modpow, productModBinomal
let inline ModInvWithPrimes (PrimeArray: ^I array) (m: ^I) (n: ^I) =
    let one = LanguagePrimitives.GenericOne
    let phi = EulerPhiWithPrimes PrimeArray m
    modpow m n (phi - one)

// mod逆数(単独)
// 依存 : EulerPhiWithPrimes, PrimesUpTo, isqrt, modpow, productModBinomal
let inline ModInv m n =
    let pa = PrimesUpTo n
    ModInvWithPrimes pa m n

// CharをIntにするだけ
let inline Char2Int c = int c - 48
// Charを小文字アルファベットの番号にするだけ
let inline Char2alphabetNum c = int c - 48
// Charを大文字アルファベットの番号にするだけ
let inline Char2AlphabetNum c = int c - 64

// 二分探索
// epsilon : 許容誤差
// ok : OK側の十分離れた値
// ng : NG側の十分離れた値
// ok側の最大値を返す
let inline BinarySearchForAny (epsilon: ^d) (isOk: ^d -> bool) (ok: ^d) (ng: ^d) =
    let one = LanguagePrimitives.GenericOne
    let two = one + one

    let rec loop (ok: ^d) (ng: ^d) =
        // printfn $"ok : {ok}  ng : {ng}"
        if abs (ok - ng) <= epsilon then
            ok
        else
            let mid = ok + (ng - ok) / two
            if isOk mid then loop mid ng else loop ok mid

    loop ok ng

let inline BinarySearch (isOk: ^d -> bool) (ok: ^d) (ng: ^d) =
    let one = LanguagePrimitives.GenericOne
    BinarySearchForAny one isOk ok ng

// Arrayに対する二分探索
let inline ArrayBinarySearch (arr: array<^d>) (isOk: ^d -> bool) (ok: int) (ng: int) =
    let one = LanguagePrimitives.GenericOne
    BinarySearchForAny one (fun i -> isOk arr.[i]) ok ng


// let countDigitsTest (num: int64) =
//     // 絶対値を取って文字列に変換し、その長さを返す
//     (abs num).ToString().Length



// グラフ走査
// neighbors (場所 -> (場所, コスト) seq ) : 隣接しているノード
// Found (場所 -> bool) : ゴールに到達したか
// push (ルート -> コスト -> メモ -> unit) : メモへの入力 (queueなら Enqueue)
// pop (メモ -> (ルート, コスト)) : メモからの出力 (queueなら Dequeue)
// note (ルート(逆順) * コスト) : メモを入れておくもの
// 返り値 : bool
let inline GraphTraversal (start: ^p) (neighbors: ^p -> (^p * ^c) seq) (Found: ^p -> bool) (push: ^p list -> ^c -> ^n -> unit) (tryPop: ^n -> (^p list * ^c) option) (note: ^n): (^p list * ^c) option =
    let zerocost = LanguagePrimitives.GenericZero

    // 初期値設定
    let exprored: Dictionary<^p,^p list> = Dictionary()
    let inList = Dictionary()
    push [start] zerocost note
    inList.Add (start, [start])

    // 探索実行
    // exprored: 探索済み
    let rec loop (exprored: Dictionary<^p, ^p list>) (inList: Dictionary<^p, ^p list>) (note: ^n) : (^p list * ^c) option =
        let nextoption = tryPop note
        match nextoption with
        | None -> None
        | Some (next, cost) ->
            if Found next.Head then
                Some (next, cost)
            else
                let neighbor = neighbors next.Head
                exprored.Add (next.Head, next)
                for n in neighbor do
                    let p, c = n
                    let route = p :: next
                    if not (exprored.ContainsKey p || inList.ContainsKey p) then
                        push route (c + cost) note
                        inList.Add (p, route)
                loop exprored inList note
    
    loop exprored inList note


/// 深さ優先探索
let inline DepthFirstSearch neighbors start found =
    let Collection = Stack<^p list>()

    let inline push (pos: ^p list) _ (collection: Stack<^p list>) = collection.Push pos

    let inline TryPop (collection: Stack<^p list>) : (^p list * ^c) option =
        let ok, result = collection.TryPop()

        if ok then
            Some(result, LanguagePrimitives.GenericOne)
        else
            None

    GraphTraversal start neighbors found push TryPop Collection

/// 幅優先探索
let inline WidthFirstSearch neighbors start found =
    let Collection = Queue<^p list>()

    let inline push (pos: ^p list) _ (collection: Queue<^p list>) = collection.Enqueue pos

    let inline TryPop (collection: Queue<^p list>) : (^p list * ^c) option =
        let ok, result = collection.TryDequeue()

        if ok then
            Some(result, LanguagePrimitives.GenericOne)
        else
            None

    GraphTraversal start neighbors found push TryPop Collection

// ダイクストラ法
// 単独で動く
let inline ShortestPathFirstSearch neighbors (start: ^p) found =
    let Collection = PriorityQueue<^p list, ^c>()

    let inline push (pos: ^p list) cost (collection: PriorityQueue<^p list, ^c>) =
        collection.Enqueue (pos, cost)

    let inline TryPop (collection: PriorityQueue<^p list, ^c>) : (^p list * ^c) option =
        let ok, result, cost = collection.TryDequeue ()
        if ok then
            Some (result, cost)
        else
            None

    let zerocost = LanguagePrimitives.GenericZero

    // 初期値設定
    let exprored: Dictionary<^p,^c * ^p list> = Dictionary()
    push [start] zerocost Collection

    // 探索実行
    // exprored: 探索済み
    let rec loop (exprored: Dictionary<^p, ^c * ^p list>) (note: PriorityQueue<^p list, ^c>) : (^p list * ^c) option =
        let nextoption = TryPop note
        match nextoption with
        | None -> None
        | Some (next, cost) ->
            if found next.Head then
                Some (next, cost)
            else
                let neighbor = neighbors next.Head
                if not (exprored.ContainsKey next.Head) then
                    exprored.Add (next.Head, (cost, next))
                    for n in neighbor do
                        let p, c = n
                        let route = p :: next
                        push route (c + cost) note
                    loop exprored  note
                elif exprored.[next.Head] |> fst > cost then
                    exprored.[next.Head] <- cost, next
                    for n in neighbor do
                        let p, c = n
                        let route = p :: next
                        push route (c + cost) note
                    loop exprored  note
                else
                    loop exprored  note
    
    loop exprored Collection



// 順列
let Permutations (r: int) (source: 'T seq) =
/// リストから要素を1つ取り出し、(取り出した要素, 残りのリスト) のリストを返すヘルパー関数
    let rec select xs =
        seq {
            match xs with
            | [] -> ()
            | head :: tail ->
                yield (head, tail)
                for (x, rest) in select tail do
                    yield (x, head :: rest)
        }
    
    let pool = Seq.toList source
    let n = List.length pool
    let targetLen = r

    if targetLen > n || targetLen < 0 then
        Seq.empty
    else
        let rec backtrack len currentPool =
            seq {
                if len = targetLen then
                    yield []
                else
                    for (item, rest) in select currentPool do
                        for path in backtrack (len + 1) rest do
                            yield item :: path
            }

        backtrack 0 pool

let combinations (r: int) (source: 'T seq) =
    let pool = Seq.toList source
    let n = List.length pool

    if r > n || r < 0 then
        Seq.empty
    else
        let rec backtrack k xs =
            seq {
                match k, xs with
                | 0, _ -> 
                    // 必要な個数を選びきった場合
                    yield []
                | _, [] -> 
                    // 選ぶ要素がなくなった場合
                    ()
                | k, head :: tail ->
                    // 1. head を選ぶパターン
                    for path in backtrack (k - 1) tail do
                        yield head :: path
                    // 2. head を選ばないパターン
                    yield! backtrack k tail
            }
        backtrack r pool

for s in combinations 3 (seq{0..5})  do
    printfn "%A" s





// 以下動作未確認

// // 桁数カウント（直接引数の型でオーバーロードを定義する）
// type DigitCounter =
//     // 32-bit 有符号整数 (int -> int)
//     [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
//     static member inline Count(n: int) : int =
//         if n = 0 then 1
//         else
//             let v = if n < 0 then -n else n
//             let bits = 32 - BitOperations.LeadingZeroCount(uint32 v)
//             let approx = (bits * 1233) >>> 12
//             let thresholds = [| 0; 9; 99; 999; 9999; 99999; 999999; 9999999; 99999999; 999999999; Int32.MaxValue |]
//             if v > thresholds.[approx] then approx + 1 else approx

//     // 32-bit 無符号整数 (uint32 -> uint32)
//     [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
//     static member inline Count(n: uint32) : uint32 =
//         if n = 0u then 1u
//         else
//             let bits = 32 - BitOperations.LeadingZeroCount(n)
//             let approx = (bits * 1233) >>> 12
//             let thresholds = [| 0u; 9u; 99u; 999u; 9999u; 99999u; 999999u; 9999999u; 99999999u; 999999999u; UInt32.MaxValue |]
//             let res = if n > thresholds.[approx] then approx + 1 else approx
//             uint32 res

//     // 64-bit 有符号整数 (int64 -> int64)
//     [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
//     static member inline Count(n: int64) : int64 =
//         if n = 0L then 1L
//         else
//             let v = if n < 0L then -n else n
//             let bits = 64 - BitOperations.LeadingZeroCount(uint64 v)
//             let res = 
//                 if bits < 21 then
//                     if bits < 14 then
//                         if bits < 7 then (if v >= 10L then 2 else 1)
//                         else (if v >= 1000L then 4 else if v >= 100L then 3 else 2)
//                     else
//                         if bits < 17 then (if v >= 100000L then 6 else if v >= 10000L then 5 else 4)
//                         else (if v >= 10000000L then 8 else if v >= 1000000L then 7 else 6)
//                 elif bits < 42 then
//                     if bits < 31 then
//                         if bits < 24 then (if v >= 1000000000L then 10 else if v >= 100000000L then 9 else 8)
//                         else (if v >= 100000000000L then 12 else if v >= 10000000000L then 11 else 10)
//                     else
//                         if bits < 35 then (if v >= 1000000000000L then 13 else 12)
//                         else (if v >= 100000000000000L then 15 else if v >= 10000000000000L then 14 else 13)
//                 else
//                     if bits < 52 then
//                         if v >= 100000000000000000L then 18 else if v >= 10000000000000000L then 17 else 16
//                     else
//                         if bits < 57 then (if v >= 1000000000000000000L then 19 else 18)
//                         else 19
//             int64 res

//     // 64-bit 無符号整数 (uint64 -> uint64)
//     [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
//     static member inline Count(n: uint64) : uint64 =
//         if n = 0UL then 1UL
//         else
//             let bits = 64 - BitOperations.LeadingZeroCount(n)
//             let res = 
//                 if bits < 21 then
//                     if bits < 14 then
//                         if bits < 7 then (if n >= 10UL then 2 else 1)
//                         else (if n >= 1000UL then 4 else if n >= 100UL then 3 else 2)
//                     else
//                         if bits < 17 then (if n >= 100000UL then 6 else if n >= 10000UL then 5 else 4)
//                         else (if n >= 10000000UL then 8 else if n >= 1000000UL then 7 else 6)
//                 elif bits < 42 then
//                     if bits < 31 then
//                         if bits < 24 then (if n >= 1000000000UL then 10 else if n >= 100000000UL then 9 else 8)
//                         else (if n >= 100000000000UL then 12 else if n >= 10000000000UL then 11 else 10)
//                     else
//                         if bits < 35 then (if n >= 1000000000000UL then 13 else 12)
//                         else (if n >= 100000000000000UL then 15 else if n >= 10000000000000UL then 14 else 13)
//                 else
//                     if bits < 52 then
//                         if n >= 100000000000000000UL then 18 else if n >= 10000000000000000UL then 17 else 16
//                     else
//                         if bits < 57 then (if n >= 1000000000000000000UL then 19 else 18)
//                         else if n >= 10000000000000000000UL then 20 else 19
//             uint64 res

//     // BigInteger (BigInteger -> BigInteger)
//     [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
//     static member inline Count(n: BigInteger) : BigInteger =
//         if n.IsZero then BigInteger.One
//         else
//             let v = BigInteger.Abs(n)
//             let bits = v.GetBitLength()
//             let approx = int ((bits * 1233L) >>> 12)
//             if v >= BigInteger.Pow(10I, approx) then BigInteger(approx + 1) else BigInteger(approx)


// // 呼び出し用インライン関数（^T -> ^T に修正）
// [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
// let inline countDigits (n: ^T) : ^T =
//     // 制約を 「^V -> ^V」 にして入力と同じ型が返るようにします
//     let inline call (helper: ^H, value: ^V) : ^V =
//         ((^H or ^V) : (static member Count : ^V -> ^V) value)
    
//     call (Unchecked.defaultof<DigitCounter>, n)







// // ニュートン法
// let NewtonRec (next : ^T -> ^T) (Check: ^T -> bool) (start: ^T) : ^T =
//     let rec loop nowAns =
//         if Check nowAns then
//             nowAns
//         else
//             loop (next nowAns)
//     loop start

// let inline NewtonCount (next : ^T -> ^T) (count: ^U) (start: ^T) : ^T =
//     let zero: ^U = LanguagePrimitives.GenericZero<^U>
//     let one: ^U = LanguagePrimitives.GenericOne<^U>
//     let rec loop (nowAns: ^T) (count: ^U) =
//         if count = zero then
//             nowAns
//         else
//             loop (next nowAns) (count - one)
//     loop start count

// let Newton (f: ^T -> ^T) (delf: ^T -> ^T) (Check: ^T -> bool) (start: ^T) : ^T =
//     NewtonRec (fun (nowAns: ^T) -> nowAns - f nowAns / delf nowAns) Check start

// // 整数型平方根(高速) O(log log n)
// let inline isqrt2 (n: ^T) : ^T =
//     // 1桁の数字の配列を生成する関数
//     let inline createSolNum (range: int) : ^T[] =
//         let solNum = Array.zeroCreate (range + 1)
//         solNum.[0] <- LanguagePrimitives.GenericZero<^T>
//         for i in 1..range do
//             solNum.[i] <- solNum.[i-1] + LanguagePrimitives.GenericOne<^T>
//         solNum

//     // 1桁の整数平方根
//     let inline soloSqrt (n: ^T) (solNum: ^T[]) =
//         if n < solNum.[1] then solNum.[0]
//         elif n < solNum.[4] then solNum.[1]
//         elif n < solNum.[9] then solNum.[2]
//         else solNum.[3]

    
//     // c : 桁数, n : 対象の数値
//     // root n | root n + 1 のいずれかを返す (多分)
//     let rec isqrt_aux c n =
//         let solNum = createSolNum 10
//         let Newton_sqrt n x = (x - n / x) / solNum.[2]

//         if c <= solNum.[1] then soloSqrt n solNum
//         else
//             // c - nextc が偶数になるように
//             // (c - nextc) / 2
//             let takec = c / solNum.[4]
//             let nextc = c - takec * solNum.[2]
//             // 上nextc桁を取るための10^n
//             let powHalf = pow solNum.[10] takec
//             let upper = n / (powHalf * powHalf)
//             let upperSqrt = isqrt_aux nextc upper * powHalf
//             NewtonCount
//                 (Newton_sqrt n)
//                 takec
//                 upperSqrt
    
//     // 桁数
//     let c = countDigits n
//     isqrt_aux c n





// // テスト
// let inline test (n: ^T) =
//     // 型指定を外すことで、自動的に n と同じ型（^T）として推論されます
//     let one = LanguagePrimitives.GenericOne<^T>
//     let zero = LanguagePrimitives.GenericZero<^T>
//     let i1 = countDigits n |> int64
//     let i2 = countDigitsTest n |> int64
//     printfn $"test {n} i1 {i1} i2 {i2} Result {abs(i1 - i2)}"
//     abs(i1 - i2) < one


// let out = HashSet<int64> ()
// let finished = HashSet<int64> ()
// let rnd = Random()

// let rec randomtest count tester =
//     if count < 0 then
//         if out.Count = 0 then printfn "Test OK"
//         else
//             for n in out do
//                 printfn $"Out : {n}"
//             printfn $"Test NG : Out count : {out.Count}"
//     else
//         let mutable target = rnd.NextInt64()
//         while finished.Contains target do
//             target <- rnd.NextInt64()
//         finished.Add target |> ignore
//         let t = tester target
//         if not t then
//             out.Add target |> ignore
//         randomtest (count-1) tester

// // ラムダ式で包んで呼び出します
// out.Clear()
// finished.Clear()
// randomtest 100 (fun (x: int64) -> test x)
