import Data.List
import Data.Function
import Cp
import List
data Blockchain = Bc {bc :: Block}  |  Bcs {bcs :: (Block, Blockchain)} deriving Show

type Block = (MagicNo, (Time, Transactions))

type Transaction = (Entity, (Value, Entity))
type Transactions = [Transaction]

type Ledger = [(Entity, Value)]

type MagicNo = String
type Time = Int  -- em milisegundos
type Entity = String
type Value = Int


inBlockchain = either Bc Bcs
outBlockchain :: Blockchain -> Either Block (Block, Blockchain)
outBlockchain (Bc a)       = i1 a
outBlockchain (Bcs (t1,t2)) = i2 (t1,t2)
baseBlockchain f g = f -|- (f >< g)
recBlockchain g = baseBlockchain id g
cataBlockchain g = g . (recBlockchain (cataBlockchain g)) . outBlockchain
anaBlockchain  g = inBlockchain . recBlockchain (anaBlockchain g) .g

allTransactions :: Blockchain -> Transactions
allTransactions = cataBlockchain (trans)
trans = either (p2.p2) (uncurry (++).(p2.p2 >< id))


ledger = cataList (either (nil) ( \((a, (b,c)), l) -> insertT (a, b) (insertT (c,-1*b) l))) . allTransactions
 where insertT (e1, val) [] = [(e1, -1 * val)]
       insertT e@(e1, val) ((ent, cash):xs) = if e1 == ent then (ent, cash - val):xs else (ent, cash): insertT e xs

ledger2 = cataList (either nil (uncurry stuff)) . cataList (either nil (uncurry (++).((\(fr, l@(quant, to)) -> (fr, (-1) * quant):swap l:[])><id))) . allTransactions
       where stuff x [] = [x]
             stuff x (h:t) = if p1 x == p1 h then (p1 h, p2 h + p2 x):t else h:stuff x t

ledger3 = cataList (either nil (\((a, (b, c)), l) -> stuff (a, -1*b) (stuff (c, b) l))). allTransactions
       where stuff x [] = [x]
             stuff x (h:t) = if p1 x == p1 h then (p1 h, p2 h + p2 x):t else h:stuff x t




isValidMagicNr =  isUnique . (cataBlockchain (either (return.p1) (uncurry(:).(p1><id))))
               where
                 isUnique [] = True
                 isUnique (x:xs) = notElem x xs && isUnique xs
