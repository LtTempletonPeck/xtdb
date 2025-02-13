package xtdb.util

import kotlin.math.max
import kotlin.math.min

class TemporalBounds {

    val validFrom: TemporalColumn = TemporalColumn()
    val validTo: TemporalColumn = TemporalColumn()
    val systemFrom: TemporalColumn = TemporalColumn()
    val systemTo: TemporalColumn = TemporalColumn()

    class TemporalColumn {
        var lower: Long = Long.MIN_VALUE
        var upper: Long = Long.MAX_VALUE

        fun lt(operand: Long) = apply { upper = min(operand - 1, upper) }
        fun lte(operand: Long) = apply { upper = min(operand, upper) }
        fun gt(operand: Long) = apply { lower = max(operand + 1, lower) }
        fun gte(operand: Long) = apply { lower = max(operand, lower) }

        fun inRange(operand: Long) = operand in lower..upper
    }

    fun inRange(validFrom: Long, validTo: Long, systemFrom: Long, systemTo: Long) =
        (this.validFrom.inRange(validFrom)
            && this.validTo.inRange(validTo)
            && this.systemFrom.inRange(systemFrom)
            && this.systemTo.inRange(systemTo))
}
