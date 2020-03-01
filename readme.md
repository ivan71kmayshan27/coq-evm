#Coq formalisation of the Ethereum Virtual Machine (WIP)

This code is an attempt to create formalisation for the Ethereum Virtual Machine by implementing a function that simulate 
consequent application of opcodes to the given execution state, call info and ethereum state mocks. Currently this implementation
is very WIP and certain important opcodes such as CALL and SHA. This implementation uses bbv for the EVM 256-bit stack cells.

## Limitations

Currently this implementation not supports calling or creating of contracts. Also, it is not designed to prove something 
with entire mainchain data, as this would involve interop with Ethereum node and lots more of complexity. 
Things that not supported yet but are planned to be added in near future: 
* Memory and persistent storage operations, currently maps for this are being added.
* Event log, should be added after memory. 
* Return data, should be added after memory.
* SHA3 hashing - not implemented since no good implementation found.
* Proofs - they are TBD.

## Currently implemented OpCodes

 * ADD	          => addActionPure state
 * MUL	          => mulActionPure state
 * SUB	          => subActionPure state
 * DIV	          => divActionPure state
 * MOD	          => modActionPure state
 * LT	          => ltActionPure state
 * GT	          => gtActionPure state
 * SLT	          => sltActionPure state
 * SGT	          => sgtActionPure state
 * EQ	          => eqActionPure state
 * ISZERO	      => iszeroActionPure state
 * AND	          => andActionPure state
 * OR	          => orActionPure state
 * XOR	          => xorActionPure state
 * NOT	          => notActionPure state
 * BYTE          => byteActionPure state
 * ADDRESS	      => addressActionPure state ci
 * ORIGIN	      => originActionPure state ci
 * CALLER	      => callerActionPure state ci
 * CALLVALUE	    => callvalueActionPure state ci
 * CALLDATASIZE	=> calldatasizeActionPure state ci
 * CODESIZE	    => codesizeActionPure state ci
 * GASPRICE	    => gaspriceActionPure state ci
 * BLOCKHASH	    => blockhashActionPure state ci
 * TIMESTAMP	    => timestampActionPure state ci
 * NUMBER	      => numberActionPure state ci
 * DIFFICULTY  	=> dificultyActionPure state ci
 * GASLIMIT	    => gaslimitActionPure state ci
 * POP	          => popActionPure state
 * PUSH arg word	=> pushActionPure arg word state
 * DUP arg	      => dupActionPure arg state
 * SWAP	arg     => swapActionPure arg state
 
## Current plans
* simple unimplemented opcodes.
* memory and persistent storage and opcodes related to opcode access.
* event log opcodes.
* return opcode.
* facts on how opcodes affect the state for most of the opcodes.

## How to use
in order to use this code you need to install Coq and then install bbv package from OPAM(http://coq.io/opam/coq-bbv.1.0.html) or from its repository(https://github.com/mit-plv/bbv)

