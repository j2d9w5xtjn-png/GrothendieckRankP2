import sys, time
sys.path.append('/mnt/data')
import rank8_search as rs
from rank8_exact import defects_to_bits, vals_to_bits, DZERO, QDIM, build_L_full, rref_with_transform, reduce_f_get_coeffs, parity
# NOTE importing rank8_exact executes its enumeration; bad. We'll copy minimal instead.
