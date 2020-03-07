##Coq formalisation of the Ethereum Virtual Machine (WIP)

This code is an attempt to create formalisation for the Ethereum Virtual Machine by implementing a function that simulate 
consequent application of opcodes to the given execution state, call info and ethereum state mocks. Currently this implementation
is very WIP and certain important opcodes such as CALL and SHA. This implementation uses bbv for the EVM 256-bit stack cells.

Opcode reference: https://ethervm.io/#96

Opcode EIP-150 gas prices: https://docs.google.com/spreadsheets/d/1n6mRqkBz3iWcOlRem_mO09GtSKEKrAsfO7Frgx18pNU/edit#gid=0

Opcode geth implementation: https://github.com/ethereum/go-ethereum/blob/master/core/vm/instructions.go
### Limitations

Currently this implementation not supports calling or creating of contracts. Also, it is not designed to prove something 
with entire mainchain data, as this would involve interop with Ethereum node and lots more of complexity. 
Things that not supported yet but are planned to be added in near future: 
* SHA3 hashing - not implemented since no good implementation found.
* Exponentiation - not yet.
* Proofs - they are TBD.

### Currently implemented OpCodes

  * ADD	          
  * MUL	          
  * SUB	          
  * DIV	          
  * SDIV	        
  * MOD	          
  * SMOD	         
  * ADDMOD	       
  * MULMOD	      
  * SIGNEXTEND	  
  * LT	          
  * GT	          
  * SLT	          
  * SGT	          
  * EQ	          
  * ISZERO	      
  * AND	          
  * OR	          
  * XOR	          
  * NOT	          
  * BYTE          
  * ADDRESS	      
  * BALANCE	      
  * ORIGIN	      
  * CALLER	      
  * CALLVALUE	    
  * CALLDATALOAD	
  * CALLDATASIZE	
  * CODESIZE	    
  * GASPRICE	    
  * EXTCODESIZE	  
  * BLOCKHASH	    
  * COINBASE	    
  * TIMESTAMP	    
  * NUMBER	      
  * DIFFICULTY  	
  * GASLIMIT	    
  * POP	          
  * MLOAD	        
  * MSTORE	      
  * MSTORE8	      
  * SLOAD	        
  * PC	           
  * MSIZE	        
  * GAS	          
  * JUMPDEST	    
  * PUSH*	
  * DUP*	      
  * SWAP*     
  * JUMP          
  * JUMPI
  * CALLDATACOPY
  * CODECOPY
  * EXTCODECOPY
  * SSTORE
  * LOG0
  * LOG1
  * LOG2
  * LOG3
  * LOG4
 
### Current plans
* finishing code for complex price opcodes, proofs
* facts on how opcodes affect the state for most of the opcodes.

### How to use
in order to use this code you need to install Coq and then install bbv package from OPAM(http://coq.io/opam/coq-bbv.1.0.html) or from its repository(https://github.com/mit-plv/bbv)

