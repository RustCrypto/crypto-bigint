//! Implementation of constant-time division via reciprocal precomputation, as described in
//! "Improved Division by Invariant Integers" by Niels Möller and Torbjorn Granlund
//! (DOI: 10.1109/TC.2010.143, https://gmplib.org/~tege/division-paper.pdf).
use subtle::{Choice, ConditionallySelectable, CtOption};

use crate::{Limb, Uint, WideWord, Word};

/// Returns `u16::MAX` if `x == y` and `0` otherwise.
#[inline(always)]
const fn ct_eq(x: u16, y: u16) -> u16 {
    // e1 == 0 if and only if x == y
    let e1 = x ^ y;

    // If e1 == 0, then e1 and -e1 are both equal to zero;
    // otherwise, one or both will have its high bit set.
    let e2 = (e1 | e1.wrapping_neg()) >> (u16::BITS - 1);

    // Result is the opposite of the high bit (now shifted to low).
    (e2 ^ 1).wrapping_neg()
}

/// Returns `a` if `c == 0` and `b` if `c == u16::MAX`.
#[inline(always)]
const fn ct_select(a: u16, b: u16, c: u16) -> u16 {
    a ^ (c & (a ^ b))
}

/// Constant-time element lookup in `arr`.
#[inline(always)]
const fn ct_lookup<const N: usize>(arr: &[u16; N], idx: u16) -> u16 {
    let mut t = arr[0];
    let mut j: u16 = 1;
    while j < N as u16 {
        t = ct_select(t, arr[j as usize], ct_eq(idx, j));
        j += 1;
    }
    t
}

/// Calculates the reciprocal of the given 32-bit divisor with the highmost bit set.
#[cfg(target_pointer_width = "32")]
pub const fn reciprocal(d: Word) -> Word {
    debug_assert!(d >= (1 << (Word::BITS - 1)));

    let d0 = d & 1;
    let d10 = d >> 22;
    let d21 = (d >> 11) + 1;
    let d31 = (d >> 1) + d0;

    let v0 = ct_lookup(&RECIPROCALS_32, (d10 & 0x1ff) as u16) as u32;
    let (hi, _lo) = mulhilo(v0 * v0, d21);
    let v1 = (v0 << 4) - hi - 1;

    // Checks that the expression for `e` can be simplified in the way we did below.
    debug_assert!(mulhilo(v1, d31).0 == (1 << 16) - 1);
    let e = Word::MAX - v1.wrapping_mul(d31) + 1 + (v1 >> 1) * d0;

    let (hi, _lo) = mulhilo(v1, e);
    // Note: the paper does not mention a wrapping add here,
    // but the 64-bit version has it at this stage, and the function panics without it
    // when calculating a reciprocal for `Word::MAX`.
    let v2 = (v1 << 15).wrapping_add(hi >> 1);

    // The paper has `(v2 + 1) * d / 2^32` (there's another 2^32, but it's accounted for later).
    // If `v2 == 2^32-1` this should give `d`, but we can't achieve this in our wrapping arithmetic.
    // Hence the `ct_select()`.
    let x = v2.wrapping_add(1);
    let (hi, _lo) = mulhilo(x, d);
    let hi = Limb::ct_select(Limb(d), Limb(hi), Limb(x).is_nonzero()).0;

    v2.wrapping_sub(hi).wrapping_sub(d)
}

/// The lookup table for 32-bit reciprocals.
/// Obtained as `(512..1024).map(|d| ((1 << 24) - (1 << 14) + (1 << 9)) / d)`.
#[cfg(target_pointer_width = "32")]
const RECIPROCALS_32: [u16; 512] = [
    32737, 32673, 32609, 32546, 32483, 32420, 32357, 32295, 32233, 32171, 32109, 32048, 31987,
    31926, 31865, 31805, 31744, 31684, 31625, 31565, 31506, 31447, 31388, 31329, 31271, 31212,
    31154, 31097, 31039, 30982, 30924, 30868, 30811, 30754, 30698, 30642, 30586, 30530, 30475,
    30419, 30364, 30309, 30255, 30200, 30146, 30092, 30038, 29984, 29930, 29877, 29824, 29771,
    29718, 29666, 29613, 29561, 29509, 29457, 29405, 29354, 29303, 29251, 29200, 29150, 29099,
    29049, 28998, 28948, 28898, 28849, 28799, 28750, 28700, 28651, 28602, 28554, 28505, 28457,
    28409, 28360, 28313, 28265, 28217, 28170, 28123, 28075, 28029, 27982, 27935, 27889, 27842,
    27796, 27750, 27704, 27658, 27613, 27568, 27522, 27477, 27432, 27387, 27343, 27298, 27254,
    27209, 27165, 27121, 27078, 27034, 26990, 26947, 26904, 26861, 26818, 26775, 26732, 26690,
    26647, 26605, 26563, 26521, 26479, 26437, 26395, 26354, 26312, 26271, 26230, 26189, 26148,
    26108, 26067, 26026, 25986, 25946, 25906, 25866, 25826, 25786, 25747, 25707, 25668, 25628,
    25589, 25550, 25511, 25473, 25434, 25395, 25357, 25319, 25281, 25242, 25205, 25167, 25129,
    25091, 25054, 25016, 24979, 24942, 24905, 24868, 24831, 24794, 24758, 24721, 24685, 24649,
    24612, 24576, 24540, 24504, 24469, 24433, 24397, 24362, 24327, 24291, 24256, 24221, 24186,
    24151, 24117, 24082, 24047, 24013, 23979, 23944, 23910, 23876, 23842, 23808, 23774, 23741,
    23707, 23674, 23640, 23607, 23574, 23541, 23508, 23475, 23442, 23409, 23377, 23344, 23312,
    23279, 23247, 23215, 23183, 23151, 23119, 23087, 23055, 23023, 22992, 22960, 22929, 22898,
    22866, 22835, 22804, 22773, 22742, 22711, 22681, 22650, 22619, 22589, 22559, 22528, 22498,
    22468, 22438, 22408, 22378, 22348, 22318, 22289, 22259, 22229, 22200, 22171, 22141, 22112,
    22083, 22054, 22025, 21996, 21967, 21938, 21910, 21881, 21853, 21824, 21796, 21767, 21739,
    21711, 21683, 21655, 21627, 21599, 21571, 21544, 21516, 21488, 21461, 21433, 21406, 21379,
    21352, 21324, 21297, 21270, 21243, 21216, 21190, 21163, 21136, 21110, 21083, 21056, 21030,
    21004, 20977, 20951, 20925, 20899, 20873, 20847, 20821, 20795, 20769, 20744, 20718, 20693,
    20667, 20642, 20616, 20591, 20566, 20540, 20515, 20490, 20465, 20440, 20415, 20390, 20366,
    20341, 20316, 20292, 20267, 20243, 20218, 20194, 20170, 20145, 20121, 20097, 20073, 20049,
    20025, 20001, 19977, 19953, 19930, 19906, 19882, 19859, 19835, 19812, 19789, 19765, 19742,
    19719, 19696, 19672, 19649, 19626, 19603, 19581, 19558, 19535, 19512, 19489, 19467, 19444,
    19422, 19399, 19377, 19354, 19332, 19310, 19288, 19265, 19243, 19221, 19199, 19177, 19155,
    19133, 19112, 19090, 19068, 19046, 19025, 19003, 18982, 18960, 18939, 18917, 18896, 18875,
    18854, 18832, 18811, 18790, 18769, 18748, 18727, 18706, 18686, 18665, 18644, 18623, 18603,
    18582, 18561, 18541, 18520, 18500, 18479, 18459, 18439, 18419, 18398, 18378, 18358, 18338,
    18318, 18298, 18278, 18258, 18238, 18218, 18199, 18179, 18159, 18139, 18120, 18100, 18081,
    18061, 18042, 18022, 18003, 17984, 17964, 17945, 17926, 17907, 17888, 17869, 17850, 17831,
    17812, 17793, 17774, 17755, 17736, 17718, 17699, 17680, 17662, 17643, 17624, 17606, 17587,
    17569, 17551, 17532, 17514, 17496, 17477, 17459, 17441, 17423, 17405, 17387, 17369, 17351,
    17333, 17315, 17297, 17279, 17261, 17244, 17226, 17208, 17191, 17173, 17155, 17138, 17120,
    17103, 17085, 17068, 17051, 17033, 17016, 16999, 16982, 16964, 16947, 16930, 16913, 16896,
    16879, 16862, 16845, 16828, 16811, 16794, 16778, 16761, 16744, 16727, 16711, 16694, 16677,
    16661, 16644, 16628, 16611, 16595, 16578, 16562, 16546, 16529, 16513, 16497, 16481, 16464,
    16448, 16432, 16416, 16400, 16384,
];

/// Calculates the reciprocal of the given 64-bit divisor with the highmost bit set.
#[cfg(target_pointer_width = "64")]
pub const fn reciprocal(d: Word) -> Word {
    debug_assert!(d >= (1 << (Word::BITS - 1)));

    let d0 = d & 1;
    let d9 = d >> 55;
    let d40 = (d >> 24) + 1;
    let d63 = (d >> 1) + d0;
    let v0 = ct_lookup(&RECIPROCALS_64, (d9 as u16) & 0xff) as u64;
    let v1 = (v0 << 11) - ((v0 * v0 * d40) >> 40) - 1;
    let v2 = (v1 << 13) + ((v1 * ((1 << 60) - v1 * d40)) >> 47);

    // Checks that the expression for `e` can be simplified in the way we did below.
    debug_assert!(mulhilo(v2, d63).0 == (1 << 32) - 1);
    let e = Word::MAX - v2.wrapping_mul(d63) + 1 + (v2 >> 1) * d0;

    let (hi, _lo) = mulhilo(v2, e);
    let v3 = (v2 << 31).wrapping_add(hi >> 1);

    // The paper has `(v3 + 1) * d / 2^64` (there's another 2^64, but it's accounted for later).
    // If `v3 == 2^64-1` this should give `d`, but we can't achieve this in our wrapping arithmetic.
    // Hence the `ct_select()`.
    let x = v3.wrapping_add(1);
    let (hi, _lo) = mulhilo(x, d);
    let hi = Limb::ct_select(Limb(d), Limb(hi), Limb(x).is_nonzero()).0;

    v3.wrapping_sub(hi).wrapping_sub(d)
}

/// The lookup table for 64-bit reciprocals.
/// Obtained as `(256..512).map(|d| ((1 << 19) - 3 * (1 << 8)) / d)`.
#[cfg(target_pointer_width = "64")]
const RECIPROCALS_64: [u16; 256] = [
    2045, 2037, 2029, 2021, 2013, 2005, 1998, 1990, 1983, 1975, 1968, 1960, 1953, 1946, 1938, 1931,
    1924, 1917, 1910, 1903, 1896, 1889, 1883, 1876, 1869, 1863, 1856, 1849, 1843, 1836, 1830, 1824,
    1817, 1811, 1805, 1799, 1792, 1786, 1780, 1774, 1768, 1762, 1756, 1750, 1745, 1739, 1733, 1727,
    1722, 1716, 1710, 1705, 1699, 1694, 1688, 1683, 1677, 1672, 1667, 1661, 1656, 1651, 1646, 1641,
    1636, 1630, 1625, 1620, 1615, 1610, 1605, 1600, 1596, 1591, 1586, 1581, 1576, 1572, 1567, 1562,
    1558, 1553, 1548, 1544, 1539, 1535, 1530, 1526, 1521, 1517, 1513, 1508, 1504, 1500, 1495, 1491,
    1487, 1483, 1478, 1474, 1470, 1466, 1462, 1458, 1454, 1450, 1446, 1442, 1438, 1434, 1430, 1426,
    1422, 1418, 1414, 1411, 1407, 1403, 1399, 1396, 1392, 1388, 1384, 1381, 1377, 1374, 1370, 1366,
    1363, 1359, 1356, 1352, 1349, 1345, 1342, 1338, 1335, 1332, 1328, 1325, 1322, 1318, 1315, 1312,
    1308, 1305, 1302, 1299, 1295, 1292, 1289, 1286, 1283, 1280, 1276, 1273, 1270, 1267, 1264, 1261,
    1258, 1255, 1252, 1249, 1246, 1243, 1240, 1237, 1234, 1231, 1228, 1226, 1223, 1220, 1217, 1214,
    1211, 1209, 1206, 1203, 1200, 1197, 1195, 1192, 1189, 1187, 1184, 1181, 1179, 1176, 1173, 1171,
    1168, 1165, 1163, 1160, 1158, 1155, 1153, 1150, 1148, 1145, 1143, 1140, 1138, 1135, 1133, 1130,
    1128, 1125, 1123, 1121, 1118, 1116, 1113, 1111, 1109, 1106, 1104, 1102, 1099, 1097, 1095, 1092,
    1090, 1088, 1086, 1083, 1081, 1079, 1077, 1074, 1072, 1070, 1068, 1066, 1064, 1061, 1059, 1057,
    1055, 1053, 1051, 1049, 1047, 1044, 1042, 1040, 1038, 1036, 1034, 1032, 1030, 1028, 1026, 1024,
];

/// Multiplies `x` and `y`, returning the most significant
/// and the least significant words as `(hi, lo)`.
#[inline(always)]
const fn mulhilo(x: Word, y: Word) -> (Word, Word) {
    let res = (x as WideWord) * (y as WideWord);
    ((res >> Word::BITS) as Word, res as Word)
}

/// Adds wide numbers represented by pairs of (most significant word, least significant word)
/// and returns the result in the same format `(hi, lo)`.
#[inline(always)]
const fn addhilo(x_hi: Word, x_lo: Word, y_hi: Word, y_lo: Word) -> (Word, Word) {
    let res = (((x_hi as WideWord) << Word::BITS) | (x_lo as WideWord))
        + (((y_hi as WideWord) << Word::BITS) | (y_lo as WideWord));
    ((res >> Word::BITS) as Word, res as Word)
}

/// Calculate the quotient and the remainder of the division of a wide word
/// (supplied as high and low words) by `d`, with a precalculated reciprocal `v`.
#[inline(always)]
const fn div2by1(u1: Word, u0: Word, reciprocal: &Reciprocal) -> (Word, Word) {
    let d = reciprocal.divisor_normalized;

    debug_assert!(d >= (1 << (Word::BITS - 1)));
    debug_assert!(u1 < d);

    let (q1, q0) = mulhilo(reciprocal.reciprocal, u1);
    let (q1, q0) = addhilo(q1, q0, u1, u0);
    let q1 = q1.wrapping_add(1);
    let r = u0.wrapping_sub(q1.wrapping_mul(d));

    let r_gt_q0 = Limb::ct_lt(Limb(q0), Limb(r));
    let q1 = Limb::ct_select(Limb(q1), Limb(q1.wrapping_sub(1)), r_gt_q0).0;
    let r = Limb::ct_select(Limb(r), Limb(r.wrapping_add(d)), r_gt_q0).0;

    let r_ge_d = Limb::ct_le(Limb(d), Limb(r));
    let q1 = Limb::ct_select(Limb(q1), Limb(q1 + 1), r_ge_d).0;
    let r = Limb::ct_select(Limb(r), Limb(r.wrapping_sub(d)), r_ge_d).0;

    (q1, r)
}

/// A pre-calculated reciprocal for division by a single limb.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Reciprocal {
    divisor_normalized: Word,
    shift: u32,
    reciprocal: Word,
}

impl Reciprocal {
    /// Pre-calculates a reciprocal for a known divisor,
    /// to be used in the single-limb division later.
    /// Returns the reciprocal, and `1` if `divisor != 0` and `0` otherwise.
    ///
    /// Note: if the returned flag is `0`, the returned reciprocal object is still self-consistent
    /// and can be passed to functions here without causing them to panic,
    /// but the results are naturally not to be used.
    pub const fn new_const(divisor: Limb) -> (Self, u8) {
        // Assuming this is constant-time for primitive types.
        let shift = divisor.0.leading_zeros();

        #[allow(trivial_numeric_casts)]
        let is_some = Limb((Word::BITS - shift) as Word).is_nonzero();

        // If `divisor = 0`, shifting `divisor` by `leading_zeros == Word::BITS` will cause a panic.
        // Have to substitute a "bogus" shift in that case.
        #[allow(trivial_numeric_casts)]
        let shift_limb = Limb::ct_select(Limb::ZERO, Limb(shift as Word), is_some);

        // Need to provide bogus normalized divisor and reciprocal too,
        // so that we don't get a panic in low-level functions.
        let divisor_normalized = divisor.shl(shift_limb);
        let divisor_normalized = Limb::ct_select(Limb::MAX, divisor_normalized, is_some).0;

        #[allow(trivial_numeric_casts)]
        let shift = shift_limb.0 as u32;

        (
            Self {
                divisor_normalized,
                shift,
                reciprocal: reciprocal(divisor_normalized),
            },
            (is_some & 1) as u8,
        )
    }

    /// Returns a default instance of this object.
    /// It is a self-consistent `Reciprocal` that will not cause panics in functions that take it.
    ///
    /// NOTE: intended for using it as a placeholder during compile-time array generation,
    /// don't rely on the contents.
    pub const fn default() -> Self {
        Self {
            divisor_normalized: Word::MAX,
            shift: 0,
            // The result of calling `reciprocal(Word::MAX)`
            // This holds both for 32- and 64-bit versions.
            reciprocal: 1,
        }
    }

    /// A non-const-fn version of `new_const()`, wrapping the result in a `CtOption`.
    pub fn new(divisor: Limb) -> CtOption<Self> {
        let (rec, is_some) = Self::new_const(divisor);
        CtOption::new(rec, Choice::from(is_some))
    }
}

impl ConditionallySelectable for Reciprocal {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            divisor_normalized: Word::conditional_select(
                &a.divisor_normalized,
                &b.divisor_normalized,
                choice,
            ),
            shift: u32::conditional_select(&a.shift, &b.shift, choice),
            reciprocal: Word::conditional_select(&a.reciprocal, &b.reciprocal, choice),
        }
    }
}

// `CtOption.map()` needs this; for some reason it doesn't use the value it already has
// for the `None` branch.
impl Default for Reciprocal {
    fn default() -> Self {
        Self::default()
    }
}

/// Divides `u` by the divisor encoded in the `reciprocal`, and returns
/// the quotient and the remainder.
#[inline(always)]
pub(crate) const fn div_rem_limb_with_reciprocal<const L: usize>(
    u: &Uint<L>,
    reciprocal: &Reciprocal,
) -> (Uint<L>, Limb) {
    let (u_shifted, u_hi) = u.shl_limb(reciprocal.shift as usize);
    let mut r = u_hi.0;
    let mut q = [Limb::ZERO; L];

    let mut j = L;
    while j > 0 {
        j -= 1;
        let (qj, rj) = div2by1(r, u_shifted.as_limbs()[j].0, reciprocal);
        q[j] = Limb(qj);
        r = rj;
    }
    (Uint::<L>::new(q), Limb(r >> reciprocal.shift))
}
