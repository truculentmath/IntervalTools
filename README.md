# IntervalTools

Mathematica code for handling infinite precision Interval objects.

Mathematica has a built-in handling of interval objects, for example Interval[{1,3}] is the closed interval of real numbers from 1 to 3. This package extends their use, assuming infinite precision endpoints, and implementing an interval version of Newton's method, the Moore-Skelboe algorithm for finding global minimums, and ProveNonNegative, a function that rigorously verifies that an expression is nonnegative.

## Metadata
      Author: Kevin O'Bryant
      Date:   May 7, 2020
      License:Feel free to use and reuse however, noncommercially, but I'd appreciate a citation if you have one to give. And prior permission for commercial use.

## Getting Started
Put IntervalTools.wl in the directory FileNameJoin[{$UserBaseDirectory, "Applications"}]

Use "<< IntervalTools`" (without the double-quotes, but with the backward quote) to load the package.

Use "?IntervalTools`*" to get a list of the added functions.

Files with "example" in their name contain examples, and the notebooks at https://www.nt.math.ubc.ca/BeMaObRe2/ contain more examples.

Unit tests are in the IntervalToolsUnitTest.nb file.
