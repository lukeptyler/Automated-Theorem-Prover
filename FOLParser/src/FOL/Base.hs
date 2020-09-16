module FOL.Base (
    module FOL.Types,
    module FOL.Substitution,
    module FOL.Rewrite
    ) where

import FOL.Types hiding (show_, show__)
import FOL.Substitution hiding (nextId, renameQuant)
import FOL.Rewrite hiding (moveQuantsToFront, isQuant, switchQuantifier)