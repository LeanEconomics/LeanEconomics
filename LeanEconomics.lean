import LeanEconomics.Basic
import Mathlib

-- Banach fixed point: the machinery behind value function iteration
#check @ContractingWith
#check @ContractingWith.fixedPoint
#check @ContractingWith.fixedPoint_isFixedPt
#check @ContractingWith.fixedPoint_unique

-- Berge / maximum theorem territory
#check @IsCompact.exists_isMaxOn