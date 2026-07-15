# Ground-truth status

The selected HumanEval set has 32 cases. The 22 verified cases are kept under
`ground_truth/`; the 10 unverified cases are kept outside the active trees under
the repository-level `archive/` directory for later work.

## Verified (22)

- p002_truncate_number
- p022_filter_integers
- p030_get_positive
- p035_max_element
- p045_triangle_area
- p053_add
- p057_monotonic
- p059_largest_prime_factor
- p060_sum_to_n
- p062_derivative
- p071_triangle_area
- p075_is_multiply_prime
- p077_iscuber
- p083_starts_one_ends
- p092_any_int
- p097_multiply
- p099_closest_integer
- p111_histogram
- p133_sum_squares
- p151_double_the_difference
- p157_right_angle_triangle
- p162_string_to_md5

## Unverified archive (10)

- p000_has_close_elements
- p004_mean_absolute_deviation
- p019_sort_numbers
- p020_find_closest_elements
- p021_rescale_to_unit
- p032_find_zero
- p037_sort_even
- p047_median
- p081_numerical_letter_grade
- p137_compare_one

The directories above are located at `archive/ground_truth/<case>/`. Their raw
and annotated inputs are likewise located at `archive/input/<case>.{c,v}` and
`archive/annotated_input/<case>.{c,v}`.

For every verified case, the case specification `.v` is kept byte-identical
across `ground_truth/<case>/<case>.v`, `input/humaneval/<case>.v`, and
`annotated_input/humaneval/<case>.v`. For every unverified case, all three paths
use their corresponding repository-level `archive/` location.
