// 二分探索
// epsilon : 許容誤差
// ok : OK側の十分離れた値
// ng : NG側の十分離れた値
// ok側の最大値を返す
// 
// isOk の例
// ((<=) n) nがあるインデックスを大きい方から探す (x -> n <= x と同じ)
// ((>=) n) nがあるインデックスを小さい方から探す
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