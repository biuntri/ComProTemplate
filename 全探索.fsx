// 順列
// r : 個数
// source : 取り出すもと
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

// 組み合わせ
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
