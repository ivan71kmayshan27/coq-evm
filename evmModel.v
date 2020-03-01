Require Import bbv.Word.
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Lt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.NArith.NArith.
Require Import Coq.Structures.OrderedType.
Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

Module M := FMapAVL.Make(N_as_OT).


(* Compute (wordToNat (wplus (natToWord 32 10) (natToWord 32 20))). *)
Definition WLen: nat := 256. 
Definition EVMWord:= word WLen.
Definition ByteLen: nat := 8.
Definition Byte := word ByteLen.
Definition WZero: EVMWord  := natToWord WLen 0.
Definition WTrue: EVMWord  := natToWord WLen 1. 
Definition WFalse: EVMWord := natToWord WLen 0. 
Definition ZeroBit: word _ := natToWord 1 0. 
Definition W0xFF: EVMWord := natToWord WLen 255.
Definition boolToWord(b: bool): EVMWord := 
  match b with 
  | true  => WTrue 
  | false => WFalse
  end.

(* Compute W0xFF. *)
Definition wgtbWorToUZ{sz: nat}(w: word sz): Z := wordToZ(bbv.Word.combine w ZeroBit).
Definition wugtb{sz: nat}(l r: word sz): bool := Z.gtb (wgtbWorToUZ l) (wgtbWorToUZ r).
Definition wultb{sz: nat}(l r: word sz): bool := Z.ltb (wgtbWorToUZ l) (wgtbWorToUZ r).
Definition wsgtb{sz: nat}(l r: word sz): bool := Z.gtb (wordToZ l) (wordToZ r).
Definition wsltb{sz: nat}(l r: word sz): bool := Z.ltb (wordToZ l) (wordToZ r).
Definition withbyte(w: EVMWord)(i: nat): EVMWord := wand (wrshift' w (248%nat - (i * 8))) W0xFF.
Definition Wones: EVMWord := wones WLen.
Definition pushMask(bytes: nat): EVMWord := wnot (wlshift' Wones (bytes * 8)).
Definition pushWordPass(w: EVMWord)(bytes: nat): EVMWord := wand (pushMask bytes) w.
(* Compute whd W0xFF. *)
Definition sextWordBytes(w: EVMWord)(bytes: nat): EVMWord := 
  match whd (wlshift' w (256 - (bytes * 8))) with 
  | true  => wor (wlshift' Wones (bytes * 8)) (pushMask bytes)
  | false => pushMask bytes
  end. 

Definition map_n_evmword := M.t EVMWord.
Definition find (k: EVMWord)(m: map_n_evmword) := M.find (wordToN k) m.
Definition update (p: EVMWord * EVMWord) (m: map_n_evmword) :=
  M.add (wordToN (fst p)) (snd p) m.
Notation "k |-> v" := (pair k v) (at level 60).
Notation "k |-> v" := (pair k v) (at level 60).
Notation "[ ]" := (M.empty nat).
Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty nat)) .. ).

Compute pushWordPass Wones 32.

Inductive Tuple2(T1 T2: Set):Set := 
  | Tuple2Mk: T1 -> T2 -> Tuple2 T1 T2.

Definition _1 {T1 T2: Set}(t: Tuple2 T1 T2): T1 := 
  match t with 
  | Tuple2Mk _ _ l _ => l
  end.

Definition _2 {T1 T2: Set}(t: Tuple2 T1 T2): T2 := 
  match t with 
  | Tuple2Mk _ _ _ r => r
  end.

Inductive Tuple3(T1 T2 T3: Set):Set := 
  | Tuple3Mk: T1 -> T2 -> T3 -> Tuple3 T1 T2 T3.

Inductive Tuple4(T1 T2 T3 T4: Set):Set := 
  | Tuple4Mk: T1 -> T2 -> T3 -> T4 -> Tuple4 T1 T2 T3 T4.

Inductive Tuple5(T1 T2 T3 T4 T5: Set):Set := 
  | Tuple5Mk: T1 -> T2 -> T3 -> T4 -> T5 -> Tuple5 T1 T2 T3 T4 T5.

Inductive Tuple6(T1 T2 T3 T4 T5 T6: Set):Set := 
  | Tuple6Mk: T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> Tuple6 T1 T2 T3 T4 T5 T6.

(* end coq tuples *)
(* straightforward either impl*)
Inductive Either(L R: Set): Set  := 
| Left: L -> Either L R
| Right: R -> Either L R.

Definition leftE{L R: Set}(e: Either L R): option L := 
  match e with 
  | Left _ _ l => Some l 
  | Right _ _ _ => None
  end.

Definition rightE{L R: Set}(e: Either L R): option R := 
  match e with 
  | Left _ _ _ => None 
  | Right _ _ r => Some r
  end.

Definition mapE{L R1 R2: Set}(e: Either L R1)(f: R1 -> R2): Either L R2 := 
  match e with
  | Left _ _ l => Left L R2 l
  | Right _ _ r => Right L R2 (f r)
  end.

Definition leftMapE{L1 L2 R: Set}(e: Either L1 R)(f: L1 -> L2): Either L2 R := 
  match e with
  | Left _ _ l => Left L2 R (f l)
  | Right _ _ r => Right L2 R r
  end.

Definition foldE{L R T: Set} (e: Either L R)(lf: L -> T)(rf: R -> T): T := 
  match e with
  | Left _ _ l => lf l
  | Right _ _ r => rf r
  end.

Definition bimapE{L1 L2 R1 R2: Set} (e: Either L1 R1)(lf: L1 -> L2)(rf: R1 -> R2): Either L2 R2 := 
  match e with
  | Left _ _ l => Left L2 R2 (lf l)
  | Right _ _ r => Right L2 R2 (rf r)
  end.

Definition flatMapE{L R: Set}(e: Either L R)(f: R -> Either L R): Either L R := 
  match e with 
  | Left _ _ l => Left L R l 
  | Right _ _ r => f r
  end.

Definition flatMapECT{L R1 R2: Set}(e: Either L R1)(f: R1 -> Either L R2): Either L R2 := 
  match e with 
  | Left _ _ l => Left L R2 l 
  | Right _ _ r => f r
  end.

Definition leftFlatMapE{L R: Set}(e: Either L R)(f: L -> Either L R): Either L R :=
  match e with 
  | Left _ _ l => f l
  | Right _ _ r => Right L R r
  end.

Definition recoverE{L R: Set}(e: Either L R)(f: L -> R): Either L R := 
  match e with
  | Left _ _ l => Right L R (f l)
  | Right _ _ r => Right L R r
  end.

Definition existsE{L R: Set}(e: Either L R)(suchAs: R -> Prop): Prop := 
  match e with 
  | Left _ _ _ => False
  | Right _ _ r => suchAs r
  end.

Definition map{L R R1: Type}(s: L + R)(f: R -> R1): L + R1 := 
  match s with 
  | inl l => inl l
  | inr r => inr (f r)
  end.

Definition flatMap{L R R1: Type}(s: L + R)(f: R -> L + R1): L + R1 := 
  match s with 
  | inl l => inl l
  | inr r => f r
  end.

Definition leftMap{L1 L2 R: Type}(s: L1+R)(f: L1 -> L2): L2 + R := 
  match s with 
  | inl l => inl (f l)
  | inr r => inr r
  end.

(* end straightforward either impl*)

(* very util functions*) 

Fixpoint compareNatsAndAct{T: Set}(a b: nat)(ifAgreaterOrEqualToB ifBgreater: T): T:= 
  match (a, b) with 
   | (O, O)            => ifAgreaterOrEqualToB 
   | (S _, O)          => ifAgreaterOrEqualToB
   | (O, S _)          => ifBgreater
   | (S predA,S predB) => compareNatsAndAct predA predB ifAgreaterOrEqualToB ifBgreater
  end.

Fixpoint gtb(a b: nat): bool := 
  match (a,b) with 
  | (O, O) => false
  | (S _, O) => true
  | (O, S _) => false
  | (S predA, S predB) => gtb predA predB
  end.

Definition flatMapO{A B: Set}(o: option A)(f: A -> option B): option B := 
  match o with 
  | Some a => f a
  | None   => None
  end. 
(* Compute let pos := 4 in let l := 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil in skipn 1 (firstn (pos - 1) l).
Compute let pos := 4 in let l := 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil in skipn pos l. *)
(* TODO: proofs  
 *)
Definition listSwapWithHead{A: Set}(l: list A)(pos: nat): option (list A) := 
  flatMapO
  (hd_error l) 
  (fun head => 
    flatMapO 
    (nth_error l pos)
    (fun item => 
      let middle := skipn 1 (firstn (pos) l) in
      let rest   := skipn (pos + 1) l in
      Some ((item :: middle) ++ (head :: rest))
    )
  ).
Compute let pos := 4 in let l := 0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil in listSwapWithHead l pos.
(* end very util functions *) 
(* execution 'monad' and error codes*)

Inductive ExecutionState: Type := 
| ExecutionStateMk: list (EVMWord) -> map_n_evmword -> map_n_evmword -> ExecutionState. (* stack memory storage*)

Definition getStack_ES es := 
match es with
| ExecutionStateMk stack _ _=> stack
end.

Definition getMemory_ES es := 
match es with
| ExecutionStateMk _ memory _=> memory
end.

Definition setStack_ES es stack := 
match es with
| ExecutionStateMk _ memory storage => ExecutionStateMk stack memory storage
end.

Definition setMemory_ES es memory := 
match es with
| ExecutionStateMk stack _ storage => ExecutionStateMk stack memory storage
end.

Definition getStorage_ES es := 
match es with
| ExecutionStateMk _ _ storage => storage
end.

Definition setStorage_ES es storage := 
match es with
| ExecutionStateMk stack memory _ => ExecutionStateMk stack memory storage
end.

Inductive SuccessfulExecutionResult: Type := 
| SuccessfulExecutionResultMk: ExecutionState -> SuccessfulExecutionResult.

Inductive ErrorCode: Set := 
| OutOfGas: ErrorCode
| InvalidOpcode: ErrorCode
| InvalidJumpDest: ErrorCode
| StackUnderflow: ErrorCode
| BadWordAsByte: ErrorCode
| BadSigExtendWord: ErrorCode
| BadByteArgI: ErrorCode
| BadShlArgI: ErrorCode
| BadShrArgI: ErrorCode
| BadCallDataLoadArgI: ErrorCode
| BadPeekArg: ErrorCode
| NonexistentAddress: ErrorCode
| NonexistentMemoryCell: ErrorCode
| NonexistentStorageCell: ErrorCode
.

Inductive ErrorneousExecutionResult: Type := 
| ErrorneousExecutionResultMk: ErrorCode -> ExecutionState -> ErrorneousExecutionResult.

Definition ExecutionResult: Type := ErrorneousExecutionResult + SuccessfulExecutionResult.

Definition OpcodeApplicationResult: Type := ExecutionResult + ExecutionState.

Definition ExecutionResultOr T : Type := ExecutionResult + T.

(* end execution 'monad' and error codes*)
(* handy constructors *) 

Definition stopExecutionWithSuccess(es: ExecutionState): OpcodeApplicationResult := 
  inl (inr (SuccessfulExecutionResultMk es)).

Definition failWithErrorCode(es: ExecutionState)(errorCode: ErrorCode): OpcodeApplicationResult :=
  inl ( inl (ErrorneousExecutionResultMk errorCode es)). 

Definition failWithErrorCodeT{T: Type} es (errorCode: ErrorCode): ExecutionResultOr T := 
  inl (inl (ErrorneousExecutionResultMk errorCode es)).

Definition runningExecutionWithState es: OpcodeApplicationResult := inr es.

Definition runningExecutionWithStateT {T: Type}(t: T): ExecutionResultOr T := inr t.
(* end handy constructors *) 
(* program counter operations *)

Definition setProgramCounter(es: ExecutionState)(programLength newPc: nat): OpcodeApplicationResult := 
    match Nat.leb programLength newPc with
    | true  => runningExecutionWithState es
    | false => failWithErrorCode es InvalidJumpDest
    end.
(* end program counter opertaions*)

(* stack operations *)
Definition pushItemToExecutionStateStack es item: ExecutionState := 
  setStack_ES es (item :: (getStack_ES es)).

Definition removeAndDropFromStackOneItem es := 
  let stack := getStack_ES es in 
    match stack with 
      | head :: tail => runningExecutionWithState (setStack_ES es tail)
      | nil => failWithErrorCode es StackUnderflow
    end.

Definition removeAndReturnFromStackOneItem es: (ExecutionResultOr (ExecutionState * EVMWord)) := 
  let stack := getStack_ES es in  
    match stack with 
      | head1 :: tail => 
          runningExecutionWithStateT ((setStack_ES es tail), head1)
      | nil => failWithErrorCodeT es StackUnderflow
    end.

Definition removeAndReturnFromStackTwoItems es: (ExecutionResultOr (ExecutionState * EVMWord * EVMWord)) := 
  let stack := getStack_ES es in 
    match stack with 
      | head1 :: head2 :: tail => 
          runningExecutionWithStateT 
            ((setStack_ES es tail), head1, head2)
      | nil | _ :: nil => failWithErrorCodeT es StackUnderflow
    end.

Definition removeAndReturnFromStackThreeItems es: (ExecutionResultOr (ExecutionState * EVMWord * EVMWord * EVMWord)) := 
  let stack := getStack_ES es in 
    match stack with 
      | head1 :: head2 :: head3:: tail => 
          runningExecutionWithStateT 
            ((setStack_ES es tail), head1, head2, head3)
      | nil | _ :: nil | _ :: _ :: nil => failWithErrorCodeT es StackUnderflow
    end.

Definition peekNthItemFromStack es (n: nat): (ExecutionResultOr EVMWord):= 
  let stack := getStack_ES es in
    match nth_error stack n with 
      | Some item => runningExecutionWithStateT item
      | None      => failWithErrorCodeT es BadPeekArg
    end.
(* end stack operations *)

Check nat.

(* WordUtil *)
Definition extractByteAsNat(w: EVMWord): ErrorCode + nat := 
  match weqb (wlshift' w 8%nat) WZero with 
  | true  => inr (wordToNat w)
  | false => inl BadWordAsByte
  end.

(* WordUtil *)
Inductive SimplePriceOpcode: Set :=
| ADD	          : SimplePriceOpcode
| MUL	          : SimplePriceOpcode
| SUB	          : SimplePriceOpcode
| DIV	          : SimplePriceOpcode
| SDIV	        : SimplePriceOpcode
| MOD	          : SimplePriceOpcode
| SMOD	        : SimplePriceOpcode
| ADDMOD	      : SimplePriceOpcode
| MULMOD	      : SimplePriceOpcode
| SIGNEXTEND	  : SimplePriceOpcode
| LT	          : SimplePriceOpcode
| GT	          : SimplePriceOpcode
| SLT	          : SimplePriceOpcode
| SGT	          : SimplePriceOpcode
| EQ	          : SimplePriceOpcode
| ISZERO	      : SimplePriceOpcode
| AND	          : SimplePriceOpcode
| OR	          : SimplePriceOpcode
| XOR	          : SimplePriceOpcode
| NOT	          : SimplePriceOpcode
| BYTE          : SimplePriceOpcode
| ADDRESS	      : SimplePriceOpcode
| BALANCE	      : SimplePriceOpcode
| ORIGIN	      : SimplePriceOpcode
| CALLER	      : SimplePriceOpcode
| CALLVALUE	    : SimplePriceOpcode
| CALLDATALOAD	: SimplePriceOpcode
| CALLDATASIZE	: SimplePriceOpcode
| CODESIZE	    : SimplePriceOpcode
| GASPRICE	    : SimplePriceOpcode
| EXTCODESIZE	  : SimplePriceOpcode
| BLOCKHASH	    : SimplePriceOpcode
| COINBASE	    : SimplePriceOpcode
| TIMESTAMP	    : SimplePriceOpcode
| NUMBER	      : SimplePriceOpcode
| DIFFICULTY  	: SimplePriceOpcode
| GASLIMIT	    : SimplePriceOpcode
| POP	          : SimplePriceOpcode
| MLOAD	        : SimplePriceOpcode
| MSTORE	      : SimplePriceOpcode
| MSTORE8	      : SimplePriceOpcode
| SLOAD	        : SimplePriceOpcode
| PC	          : SimplePriceOpcode
| MSIZE	        : SimplePriceOpcode
| GAS	          : SimplePriceOpcode
| JUMPDEST	    : SimplePriceOpcode
| PUSH	        : word 5 -> EVMWord -> SimplePriceOpcode
| DUP	          : word 4 -> SimplePriceOpcode
| SWAP	        : word 4 -> SimplePriceOpcode
| CREATE	      : SimplePriceOpcode
.

Definition simplePriceOpcodePrice(o: SimplePriceOpcode): nat :=
  match o with
  | ADD	          => 3
  | MUL	          => 5
  | SUB	          => 3
  | DIV	          => 5
  | SDIV	        => 5
  | MOD	          => 5
  | SMOD	        => 5
  | ADDMOD	      => 8
  | MULMOD	      => 8
  | SIGNEXTEND	  => 5
  | LT	          => 3
  | GT	          => 3
  | SLT	          => 3
  | SGT	          => 3
  | EQ	          => 3
  | ISZERO	      => 3
  | AND	          => 3
  | OR	          => 3
  | XOR	          => 3
  | NOT	          => 3
  | BYTE          => 3
  | ADDRESS	      => 2
  | BALANCE	      => 400
  | ORIGIN	      => 2
  | CALLER	      => 2
  | CALLVALUE	    => 2
  | CALLDATALOAD	=> 3
  | CALLDATASIZE	=> 2
  | CODESIZE	    => 2
  | GASPRICE	    => 2
  | EXTCODESIZE	  => 700
  | BLOCKHASH	    => 20
  | COINBASE	    => 2
  | TIMESTAMP	    => 2
  | NUMBER	      => 2
  | DIFFICULTY  	=> 2
  | GASLIMIT	    => 2
  | POP	          => 2
  | MLOAD	        => 3
  | MSTORE	      => 3
  | MSTORE8	      => 3
  | SLOAD	        => 200
  | PC	          => 2
  | MSIZE	        => 2
  | GAS	          => 2
  | JUMPDEST	    => 1
  | PUSH _ _	    => 3
  | DUP _	        => 3
  | SWAP	_       => 3
  | CREATE	      => 32000
  end.

Inductive ComplexPriceOpcode: Set :=
|	EXP                : ComplexPriceOpcode
|	SHA3	             : ComplexPriceOpcode
|	CALLDATACOPY	     : ComplexPriceOpcode
|	CODECOPY	         : ComplexPriceOpcode
|	EXTCODECOPY	       : ComplexPriceOpcode
|	SSTORE	           : ComplexPriceOpcode
|	LOG0	             : ComplexPriceOpcode
|	LOG1	             : ComplexPriceOpcode
|	LOG2	             : ComplexPriceOpcode
|	LOG3	             : ComplexPriceOpcode
|	LOG4	             : ComplexPriceOpcode
|	CALL	             : ComplexPriceOpcode
|	CALLCODE	         : ComplexPriceOpcode
|	DELEGATECALL	     : ComplexPriceOpcode
|	SELFDESTRUCT	     : ComplexPriceOpcode
.


Inductive OpCode: Set :=
|	STOP	              : OpCode
|	RETURN	            : OpCode
| JUMP	              : OpCode
| JUMPI	              : OpCode
| ComplexPriceOpcodeMk: ComplexPriceOpcode -> OpCode
| SimplePriceOpcodeMk : SimplePriceOpcode  -> OpCode
.

Inductive CallInfo: Type := 
| CallInfoMk: 
  list (EVMWord)(*calldata*) ->
  EVMWord(*this contract address*) ->
  EVMWord(*caller balance*) ->
  EVMWord(*transaction hash*) ->
  EVMWord(*caller address*) ->
  EVMWord(*call eth value*) ->
  list Byte(*this contract code*) ->
  EVMWord(*tx gas price*) ->
  EVMWord(*block hash*) ->
  EVMWord(*block number*) ->
  EVMWord(*block dificulty*) ->
  EVMWord(*block timestamp*) ->
  EVMWord(*gas block limit*) ->
  EVMWord(*miner's address*) ->
  map_n_evmword(*account balances *) -> 
  CallInfo.

(* 
  match _ with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
  end
 *)
Definition get_calldata(ci: CallInfo): list EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    calldata
  end.

Definition get_thisContractAddress(ci: CallInfo): EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    thisContractAddress
  end.

Definition get_callerBalance(ci: CallInfo): EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    callerBalance
  end.

Definition get_transactionHash(ci: CallInfo): EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    transactionHash
  end.

Definition get_callerAddress(ci: CallInfo): EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    callerAddress
  end.

Definition get_callEthValue(ci: CallInfo): EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    callEthValue
  end.

Definition get_thisContractCode(ci: CallInfo): list (word ByteLen) := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    thisContractCode
  end.

Definition get_txGasPrice(ci: CallInfo): EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    txGasPrice
  end.

Definition get_blockHash(ci: CallInfo):EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    blockHash
  end.

Definition get_blockNumber(ci: CallInfo): EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    blockNumber
  end.

Definition get_blockDificulty(ci: CallInfo): EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    blockDificulty
  end.

Definition get_gasLimit(ci: CallInfo): EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    blockDificulty
  end.

Definition get_miner(ci: CallInfo): EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    miner
  end.

Definition get_blockTimestamp(ci: CallInfo): EVMWord := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    blockTimestamp
  end.

Definition get_accountBalances(ci: CallInfo): map_n_evmword := 
  match ci with 
  | CallInfoMk calldata thisContractAddress callerBalance transactionHash callerAddress callEthValue thisContractCode txGasPrice blockHash blockNumber blockDificulty blockTimestamp gasLimit miner accountBalances=> 
    accountBalances
  end.

Definition stopAction(state: ExecutionState): OpcodeApplicationResult := 
  stopExecutionWithSuccess (state).

Definition addActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    ( fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (wplus a b))  
      end
    ).

Definition mulActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (wmult a b))  
      end
    ).

Definition subActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (wminus a b))  
      end
    ).

Definition divActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (wdiv a b))  
      end
    ).

Definition sdivActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (wdivZ a b))  
      end
    ).

Definition modActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (wmod a b))  
      end
    ).

Definition smodActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap 
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (ZToWord WLen (Z.rem (wordToZ a) (wordToZ b))))  
      end
    ).

Definition addmodActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap 
    (removeAndReturnFromStackThreeItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b, N) => 
      let za := wordToZ a in let zb := wordToZ b in let zN := Z.of_N (wordToN N) in 
      let zres := Z.rem (za + zb) zN in
      runningExecutionWithState (pushItemToExecutionStateStack es (ZToWord WLen zres))  
      end
    ).

Definition mulmodActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap 
    (removeAndReturnFromStackThreeItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b, N) => 
      let za := wordToZ a in let zb := wordToZ b in let zN := Z.of_N (wordToN N) in 
      let zres := Z.rem (za * zb) zN in
      runningExecutionWithState (pushItemToExecutionStateStack es (ZToWord WLen zres))  
      end
    ).

Definition signextendActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap 
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => 
        match extractByteAsNat b with 
        | inl err => failWithErrorCode es err
        | inr n   => runningExecutionWithState (pushItemToExecutionStateStack es (sextWordBytes a n))
        end
      end
    ).

Definition ltActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (boolToWord (wultb a b)))  
      end
    ).

Definition gtActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (boolToWord (wugtb a b)))  
      end
    ).


Definition sltActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (boolToWord (wsltb a b)))  
      end
    ).

Definition sgtActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (boolToWord (wsgtb a b)))  
      end
    ).


Definition eqActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (boolToWord (weqb a b)))  
      end
    ).

Definition iszeroActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackOneItem state)
    (fun tup2 => 
      match tup2 with 
      | (es, a) => runningExecutionWithState (pushItemToExecutionStateStack es (boolToWord (weqb a WZero)))  
      end
    ).

Definition andActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (wand a b))  
      end
    ).

Definition orActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (wor a b))  
      end
    ).

Definition xorActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, a, b) => runningExecutionWithState (pushItemToExecutionStateStack es (wxor a b))  
      end
    ).

Definition notActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackOneItem state)
    (fun tup2 => 
      match tup2 with 
      | (es, a) => runningExecutionWithState (pushItemToExecutionStateStack es (wnot a))  
      end
    ).

Definition byteActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, i, x) => 
        match extractByteAsNat i with 
        | inr inat    => 
            match Nat.ltb inat 32 with 
            | true  => runningExecutionWithState (pushItemToExecutionStateStack es (withbyte x inat)) 
            | false => failWithErrorCode es BadShlArgI
            end
        | inl errCode => failWithErrorCode es errCode
        end
      end
    ).

Definition shlActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, i, x) => 
        match extractByteAsNat i with 
        | inr inat    => 
            match Nat.ltb inat 257 with 
            | true  => runningExecutionWithState (pushItemToExecutionStateStack es (wlshift' x inat)) 
            | false => failWithErrorCode es BadShrArgI
            end
        | inl errCode => failWithErrorCode es errCode
        end
      end
    ).

Definition shrActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, i, x) => 
        match extractByteAsNat i with 
        | inr inat    => 
            match Nat.ltb inat 257 with 
            | true  => runningExecutionWithState (pushItemToExecutionStateStack es (wrshift' x inat)) 
            | false => failWithErrorCode es BadByteArgI
            end
        | inl errCode => failWithErrorCode es errCode
        end
      end
    ).

(*SHA3*)
Definition addressActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
  runningExecutionWithState (pushItemToExecutionStateStack state (get_thisContractAddress ci)).

Definition balanceActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult :=
  flatMap 
  (removeAndReturnFromStackOneItem state)
  (fun tup2 => 
      match tup2 with 
      | (es, a) => 
        match find a (get_accountBalances ci) with
        | Some balance => runningExecutionWithState (pushItemToExecutionStateStack es balance)  
        | None => failWithErrorCode es NonexistentAddress
        end
      end
    ).
  
Definition originActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
  runningExecutionWithState (pushItemToExecutionStateStack state (get_callerAddress ci)).

(*  becasue currently implemnted state of EVM does not support nested contract calls, callser = origin *)
Definition callerActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
  runningExecutionWithState (pushItemToExecutionStateStack state (get_callerAddress ci)).

Definition callvalueActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
  runningExecutionWithState (pushItemToExecutionStateStack state (get_callEthValue ci)).

Definition calldataloadActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackOneItem state)
    (fun tup2 => 
      match tup2 with (* todo complete*)
      | (es, idxWord) => 
        let i := wordToNat idxWord in 
          match nth_error (get_calldata ci) i with 
          | Some dataCell => runningExecutionWithState (pushItemToExecutionStateStack es dataCell)  
          | None          => failWithErrorCode es BadCallDataLoadArgI
          end
      end
    ).

Definition calldatasizeActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
    runningExecutionWithState (pushItemToExecutionStateStack state (natToWord WLen (length (get_calldata ci)))).

(*Calldatacopy*)

Definition codesizeActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
    runningExecutionWithState (pushItemToExecutionStateStack state (natToWord WLen (length (get_thisContractCode ci)))).
(* codecopy *)

Definition gaspriceActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
    runningExecutionWithState (pushItemToExecutionStateStack state (get_txGasPrice ci)).

(* extcodesize *)
(* extcodecopy *)

Definition blockhashActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
    runningExecutionWithState (pushItemToExecutionStateStack state (get_blockHash ci)).

Definition coinbaseActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
    runningExecutionWithState (pushItemToExecutionStateStack state (get_miner ci)).

Definition timestampActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
    runningExecutionWithState (pushItemToExecutionStateStack state (get_blockTimestamp ci)).

Definition numberActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
    runningExecutionWithState (pushItemToExecutionStateStack state (get_blockNumber ci)).

Definition dificultyActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
    runningExecutionWithState (pushItemToExecutionStateStack state (get_blockDificulty ci)).

Definition gaslimitActionPure(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
    runningExecutionWithState (pushItemToExecutionStateStack state (get_gasLimit ci)).

Definition popActionPure(state: ExecutionState): OpcodeApplicationResult := 
    flatMap
    (removeAndReturnFromStackOneItem state)
    (fun tup2 => 
      runningExecutionWithState (fst tup2)
    ).

Definition mloadActionPure(state: ExecutionState): OpcodeApplicationResult := 
  flatMap 
  (removeAndReturnFromStackOneItem state)
    (fun tup2 => 
      match tup2 with 
      | (es, key) => 
        match find key (getMemory_ES es) with
        | Some wrd => runningExecutionWithState (pushItemToExecutionStateStack state wrd)
        | None     => failWithErrorCode es NonexistentMemoryCell
        end
      end
    ).

Definition mstoreActionPure(state: ExecutionState): OpcodeApplicationResult := 
  flatMap 
  (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, key, value) => runningExecutionWithState (setMemory_ES es (update (key, value) (getMemory_ES es)) )
      end
    ).

Definition mstore8ActionPure(state: ExecutionState): OpcodeApplicationResult := 
  flatMap 
  (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, key, value) => runningExecutionWithState (setMemory_ES es (update (key, wand value W0xFF) (getMemory_ES es)) )
      end
    ).


Definition sloadActionPure(state: ExecutionState): OpcodeApplicationResult := 
  flatMap 
  (removeAndReturnFromStackOneItem state)
    (fun tup2 => 
      match tup2 with 
      | (es, key) => 
        match find key (getStorage_ES es) with
        | Some wrd => runningExecutionWithState (pushItemToExecutionStateStack state wrd)
        | None     => failWithErrorCode es NonexistentMemoryCell
        end
      end
    ).

Definition sstoreActionPure(state: ExecutionState): OpcodeApplicationResult := 
  flatMap 
  (removeAndReturnFromStackTwoItems state)
    (fun tup3 => 
      match tup3 with 
      | (es, key, value) => runningExecutionWithState (setStorage_ES es (update (key, value) (getStorage_ES es)) )
      end
    ).

(* PC *) 
(* MSIZE *)
(* GAS *)

Definition pushActionPure(bytes: word 5)(w: EVMWord)(state: ExecutionState): OpcodeApplicationResult :=
  let checkedWord := pushWordPass w (wordToNat bytes + 1) in 
  runningExecutionWithState (pushItemToExecutionStateStack state checkedWord).

Definition dupActionPure(bytes: word 4)(state: ExecutionState):OpcodeApplicationResult := 
  flatMap
  (peekNthItemFromStack state (wordToNat bytes)) 
  (fun item => 
    runningExecutionWithState (pushItemToExecutionStateStack state item)
  ).

Definition swapActionPure(bytes: word 4)(state: ExecutionState): OpcodeApplicationResult := 
   let stack := getStack_ES state in 
   match listSwapWithHead(stack)((wordToNat bytes) + 1)  with 
   | Some swappedStack => runningExecutionWithState (setStack_ES state swappedStack)
   | None              => failWithErrorCode state BadPeekArg
   end.

(* LOG*) 
(* CREATE *)
(* CALL *)
(* CALLCODE*)
(*RETURN*)
(*DELEGATECALL*)
(*SELFDESTRUCT*)
Definition opcodeProgramStateChange(opc: SimplePriceOpcode)(state: ExecutionState)(ci: CallInfo): OpcodeApplicationResult := 
  match opc with 
  | ADD	          => addActionPure state
  | MUL	          => mulActionPure state
  | SUB	          => subActionPure state
  | DIV	          => divActionPure state
  | SDIV	        => sdivActionPure state
  | MOD	          => modActionPure state
  | SMOD	        => smodActionPure state 
  | ADDMOD	      => addmodActionPure state 
  | MULMOD	      => mulmodActionPure state
  | SIGNEXTEND	  => signextendActionPure state
  | LT	          => ltActionPure state
  | GT	          => gtActionPure state
  | SLT	          => sltActionPure state
  | SGT	          => sgtActionPure state
  | EQ	          => eqActionPure state
  | ISZERO	      => iszeroActionPure state
  | AND	          => andActionPure state
  | OR	          => orActionPure state
  | XOR	          => xorActionPure state
  | NOT	          => notActionPure state
  | BYTE          => byteActionPure state
  | ADDRESS	      => addressActionPure state ci
  | BALANCE	      => balanceActionPure state ci
  | ORIGIN	      => originActionPure state ci
  | CALLER	      => callerActionPure state ci
  | CALLVALUE	    => callvalueActionPure state ci
  | CALLDATALOAD	=> calldataloadActionPure state ci
  | CALLDATASIZE	=> calldatasizeActionPure state ci
  | CODESIZE	    => codesizeActionPure state ci
  | GASPRICE	    => gaspriceActionPure state ci
  | EXTCODESIZE	  => stopExecutionWithSuccess (state) (* TODO implement *)
  | BLOCKHASH	    => blockhashActionPure state ci
  | COINBASE	    => coinbaseActionPure state ci
  | TIMESTAMP	    => timestampActionPure state ci
  | NUMBER	      => numberActionPure state ci
  | DIFFICULTY  	=> dificultyActionPure state ci
  | GASLIMIT	    => gaslimitActionPure state ci
  | POP	          => popActionPure state
  | MLOAD	        => mloadActionPure state
  | MSTORE	      => mstoreActionPure state
  | MSTORE8	      => mstore8ActionPure state
  | SLOAD	        => sloadActionPure state
  | PC	          => stopExecutionWithSuccess (state) (* TODO implement *)
  | MSIZE	        => stopExecutionWithSuccess (state) (* TODO implement *)
  | GAS	          => stopExecutionWithSuccess (state) (* TODO implement *)
  | JUMPDEST	    => stopExecutionWithSuccess (state) (* TODO implement *)
  | PUSH arg word	=> pushActionPure arg word state
  | DUP arg	      => dupActionPure arg state
  | SWAP	arg     => swapActionPure arg state
  | CREATE	      => stopExecutionWithSuccess (state) (* TODO implement *)
(*   | _   => stopExecutionWithSuccess (state) *)
  end.

(* Super ugly but i don't wan to bother with well-founded stuff.*)
(* Check Nat.eqb.
Check bool. *)

Fixpoint actOpcode(gas programCounter: nat)(ec: ExecutionState)(program: list OpCode)(callInfo: CallInfo){struct gas}: ExecutionResult :=
    match gas with 
    | S predGas => 
      match (nth_error program programCounter) with 
      | Some opc => 
        match opc with 
        | STOP                        => inr (SuccessfulExecutionResultMk ec)
        |	RETURN	                    => inr (SuccessfulExecutionResultMk ec) (* TODO change to return memory region *)
        | JUMP	                      => inr (SuccessfulExecutionResultMk ec) (* TODO change to unconditional jump *)
        | JUMPI	                      => inr (SuccessfulExecutionResultMk ec) (* TODO change to conditional jump *)
        | ComplexPriceOpcodeMk opcode => inr (SuccessfulExecutionResultMk ec) (* TODO change to the opcodes implementation*)
        | SimplePriceOpcodeMk opcode  => 
          match opcodeProgramStateChange opcode ec callInfo with 
          | inl result       => result
          | inr updatedState => (* reduce gas and go on*)(* gas - gasCost = (gas - 1) - (gasCost - 1)*)
            actOpcode (predGas - ((simplePriceOpcodePrice opcode) -1)) (S programCounter) updatedState program callInfo
          end
        end
      | None     => inl (ErrorneousExecutionResultMk InvalidJumpDest ec)
      end
    | O         => 
      match (Nat.eqb programCounter (S(length program))) with 
      | true  => inr (SuccessfulExecutionResultMk ec)
      | false => inl (ErrorneousExecutionResultMk  OutOfGas ec)
      end
    end.

Fixpoint actOpcodeWithInstructionsLimitation(maxinstructions gas programCounter: nat)(ec: ExecutionState)(program: list OpCode)(callInfo: CallInfo){struct maxinstructions}: ExecutionResult :=
    match maxinstructions with 
    | S instructionsLeft => 
      match (nth_error program programCounter) with 
      | Some opc => 
        match opc with 
        | STOP                        => inr (SuccessfulExecutionResultMk ec)
        |	RETURN	                    => inr (SuccessfulExecutionResultMk ec) (* TODO change to return memory region *)
        | JUMP	                      => inr (SuccessfulExecutionResultMk ec) (* TODO change to unconditional jump *)
        | JUMPI	                      => inr (SuccessfulExecutionResultMk ec) (* TODO change to conditional jump *)
        | ComplexPriceOpcodeMk opcode => inr (SuccessfulExecutionResultMk ec) (* TODO change to the opcodes implementation*)
        | SimplePriceOpcodeMk opcode  => 
          match opcodeProgramStateChange opcode ec callInfo with 
          | inl result       => result
          | inr updatedState => (* reduce gas and go on*)(* gas - gasCost = (gas - 1) - (gasCost - 1)*)
            let gasLeft := gas - (simplePriceOpcodePrice opcode) in
            let gasPositive := Nat.ltb (simplePriceOpcodePrice opcode) gas in 
            let gasZero := Nat.eqb gas (simplePriceOpcodePrice opcode) in 
            let over := Nat.eqb programCounter (S(length program)) in 
              match (gasPositive, gasZero, over) with 
              | (true, _, _)     => actOpcodeWithInstructionsLimitation (instructionsLeft)(gasLeft)(S programCounter) updatedState program callInfo
              | (_, true, true)  => inr (SuccessfulExecutionResultMk ec)
              | (false, _, _)    => inl (ErrorneousExecutionResultMk  OutOfGas ec)
              end
            
          end
        end
      | None     => inl (ErrorneousExecutionResultMk InvalidJumpDest ec)
      end
    | O         => 
      match (Nat.eqb programCounter (S(length program))) with 
      | true  => inr (SuccessfulExecutionResultMk ec)
      | false => inl (ErrorneousExecutionResultMk  OutOfGas ec)
      end
    end. 


(*
Fixpoint executeProgram(gas: nat)(initialState: ExecutionState)(program: list OpCode): OpcodeApplicationResult := 
  match initialState with 
  | ExecutionStateMk pc _ =>  
    match (nth_error program pc) with
    | Some opcode => 
      flatMapE _ _
      (opcodeProgramStateChange opcode initialState )
      (fun state => executeProgram state program)
    | None => failWithErrorCode initialState OutOfGas
    end
  end.*)