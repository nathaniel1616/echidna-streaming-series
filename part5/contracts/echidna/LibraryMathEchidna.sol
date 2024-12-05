// SPDX-License-Identifier: GPL-3.0-only
pragma solidity 0.8.6;

import "../libraries/Reserve.sol";

contract LibraryMathEchidna {
    Reserve.Data private reserve = Reserve.Data(0, 0, 0, 0, 0, 0, 0);
    bool isSetup;

    // event LogReserve(Reserve.Data reserve);
    event LogUint256(string text, uint256 value);
    event AssertionFailed(string message, uint256 actual, uint256 expected);
    event LogPreAndPostUint256(string text, uint256 pre, uint256 post);

    function setupReserve() private {
        reserve.reserveRisky = 1 ether;
        reserve.reserveStable = 2 ether;
        reserve.liquidity = 4 ether;
        isSetup = true;
    }

    function safepath_reserve_allocate(
        uint256 delRisky, // uint256 argument
        uint256 delStable
    ) public returns (Reserve.Data memory preAllocateReserves, uint256 delLiquidity) {
        //************************* Pre-Conditions *************************/
        // INVARIANT: isSetup has to be true(0,0,0,0,0,0,)
        if (!isSetup) setupReserve();
        // INVARIANT: delRisky, delStable need to be >0
        delRisky = _between(delRisky, 1, type(uint128).max);
        delStable = _between(delStable, 1, type(uint128).max);
        uint256 liquidity0 = (delRisky * reserve.liquidity) / uint256(reserve.reserveRisky); // calculate the risky token spot price , @nat invariant reserve.reserveRisky > 0
        uint256 liquidity1 = (delStable * reserve.liquidity) / uint256(reserve.reserveStable); // calculate the stable token spot price
        delLiquidity = liquidity0 < liquidity1 ? liquidity0 : liquidity1; // min(risky,stable)
        // INVARIANT: delta liquidity needs to be >0.
        // snapshot the pool
        preAllocateReserves = reserve;
        uint128 preReserveRisky = preAllocateReserves.reserveRisky;
        uint128 preReserveStable = preAllocateReserves.reserveStable;
        uint128 preReserveLiquidity = preAllocateReserves.liquidity;
        //************************* Action *************************/

        Reserve.allocate(reserve, delRisky, delStable, delLiquidity, uint32(block.timestamp + 1000)); //@note INVARIANT: increase reserves and liquidity amounts for the pool

        //************************* Post-Conditions *************************/
        // reserveRisky should increase;

        uint256 postReserveRisky = preReserveRisky + delRisky;
        // reserveStable should increase
        uint256 postReserveStable = preReserveStable + delStable;
        // liquidity should increase
        uint256 postLiquidity = preReserveLiquidity + delLiquidity;

        assert(reserve.reserveRisky == postReserveRisky);
        assert(reserve.reserveStable == postReserveStable);
        assert(reserve.liquidity == postLiquidity);
    }

    function unSafepath_reserve_allocate(
        uint256 delRisky, // uint256 argument
        uint256 delStable
    ) public returns (Reserve.Data memory preAllocateReserves, uint256 delLiquidity) {
        //************************* Pre-Conditions *************************/
        // INVARIANT: delRisky, delStable need to be >0
        delRisky = _between(delRisky, 1, type(uint256).max);
        delStable = _between(delStable, 1, type(uint256).max);
        uint256 liquidity0 = (delRisky * reserve.liquidity) / uint256(reserve.reserveRisky); // calculate the risky token spot price , @nat invariant reserve.reserveRisky > 0
        uint256 liquidity1 = (delStable * reserve.liquidity) / uint256(reserve.reserveStable); // calculate the stable token spot price
        delLiquidity = liquidity0 < liquidity1 ? liquidity0 : liquidity1; // min(risky,stable)
        // INVARIANT: delta liquidity needs to be >0.
        // snapshot the pool
        preAllocateReserves = reserve;

        //************************* Action *************************/

        Reserve.allocate(reserve, delRisky, delStable, delLiquidity, uint32(block.timestamp + 1000)); //@note INVARIANT: increase reserves and liquidity amounts for the pool

        //************************* Post-Conditions *************************/
        // reserveRisky should increase;

        assert(reserve.reserveRisky == preAllocateReserves.reserveRisky + delRisky);
        assert(reserve.reserveStable == preAllocateReserves.reserveStable + delStable);
        assert(reserve.liquidity == preAllocateReserves.liquidity + delLiquidity);
    }

    function reserve_remove(uint256 delLiquidity)
        public
        returns (Reserve.Data memory postAllocateReserves, uint256 delRisky, uint256 delStable)
    {
        //************************* Pre-Conditions *************************/
        // INVARIANT: isSetup has to be true , since the reserve should have funds
        if (!isSetup) setupReserve();
        //@note INVARIANT: the change in liquidity must be > 0
        // calculates the amount of risky and stable in exchange for liquidity

        // snapshot the pool
        Reserve.Data memory postAllocateReserves = reserve;
        // delLiquidity = _between(delLiquidity, 1, uint128(reserve.liquidity));
        delLiquidity = _between(delLiquidity, 1, type(uint128).max);
        (delRisky, delStable) = Reserve.getAmounts(reserve, delLiquidity);
        // decrease the amount of liquidity associated to a pool
        //@note INVARIANT: risky, stable, liquidity amounts for a pool should decrease by respective amounts
        //@note INVARIANT: margins for the msg.sender should increase
        //************************* Action *************************/
        Reserve.remove(reserve, delRisky, delStable, delLiquidity, uint32(block.timestamp + 1000));
        //************************* Post-Conditions *************************/
        //@note INVARIANT: the change in liquidity must be > 0

        assert(reserve.reserveRisky == postAllocateReserves.reserveRisky - delRisky);
        assert(reserve.reserveStable == postAllocateReserves.reserveStable - delStable);
        assert(reserve.liquidity == postAllocateReserves.liquidity - delLiquidity);
        //@note INVARIANT: risky, stable, liquidity amounts for a pool should decrease by respective amounts
        //@note INVARIANT: margins for the msg.sender should increase
    }

    function allocate_then_remove(
        uint256 delRisky, // uint256 argument
        uint256 delStable
    ) public {
        //************************* Pre-Conditions************************ */
        // the input bound will be checked in the saafepath_reserve_allocate
        //************************* Actions*************************/
        (Reserve.Data memory preAllocateReserves, uint256 delAllocateLiquidity) =
            safepath_reserve_allocate(delRisky, delStable);
        (Reserve.Data memory postAllocateReserves, uint256 delRiskyPostRemove, uint256 delStablePostRemove) =
            reserve_remove(delAllocateLiquidity);

        //************************* Post-Conditions*************************/
        //  snapshot1 ( postRemove (allocating and removing) ie current reserve state) state changes should be the same as preAllocate state
        Reserve.Data memory postAllocateAndRemoveReserves = reserve;

        emit LogPreAndPostUint256("liquidity", preAllocateReserves.liquidity, postAllocateAndRemoveReserves.liquidity);
        emit LogPreAndPostUint256(
            "reserveStable", preAllocateReserves.reserveStable, postAllocateAndRemoveReserves.reserveStable
        );
        emit LogPreAndPostUint256(
            "reserveRisky", preAllocateReserves.reserveRisky, postAllocateAndRemoveReserves.reserveRisky
        );

        if (preAllocateReserves.liquidity != postAllocateAndRemoveReserves.liquidity) {
            emit AssertionFailed(
                "preAllocateReserves.liquidity != postAllocateAndRemoveReserves.liquidity",
                preAllocateReserves.liquidity,
                postAllocateAndRemoveReserves.liquidity
            );
        }

        if (preAllocateReserves.reserveStable != postAllocateAndRemoveReserves.reserveStable) {
            emit AssertionFailed(
                "preAllocateReserves.reserveStable == postAllocateAndRemoveReserves.reserveStable",
                preAllocateReserves.reserveStable,
                postAllocateAndRemoveReserves.reserveStable
            );
        }

        if (preAllocateReserves.reserveRisky != postAllocateAndRemoveReserves.reserveRisky) {
            emit AssertionFailed(
                "preAllocateReserves.reserveRisky != postAllocateAndRemoveReserves.reserveRisky",
                preAllocateReserves.reserveRisky,
                postAllocateAndRemoveReserves.reserveRisky
            );
        }
    }

    function _between(uint256 random, uint256 low, uint256 high) private pure returns (uint256) {
        return low + random % (high - low);
    }
}
