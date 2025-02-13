package xtdb.vector

interface IVectorIndirection {
    fun valueCount(): Int

    fun getIndex(idx: Int): Int

    operator fun get(idx: Int): Int = getIndex(idx)

    data class Selection(val idxs: IntArray) : IVectorIndirection {
        override fun valueCount(): Int {
            return idxs.size
        }

        override fun getIndex(idx: Int): Int {
            return idxs[idx]
        }

        override fun toString(): String {
            val idxs =  idxs.contentToString()
            return "(Selection {idxs=$idxs})"
        }
    }

    data class Slice(val startIdx: Int, val len: Int) : IVectorIndirection {
        override fun valueCount(): Int {
            return len
        }

        override fun getIndex(idx: Int): Int {
            return startIdx + idx
        }
    }
}
