//! Regression tests for the zipper iteration-token fixes that followed PR #74 (head fad58f4).
//! Each test failed on that head and passes with the accompanying fixes.
use pathmap::PathMap;
use pathmap::zipper::*;

// ---- Bug 1 (new in 662e593): after_focus descendant skip fires for a nonexistent lower-bound token
#[test] fn b1_next_sibling_from_missing_path_between_key0_and_descendant_key1() {
    let m: PathMap<()> = [&b"a"[..], b"abcd"].into_iter().collect();
    let mut z = m.read_zipper();
    z.descend_to(b"aa");
    assert!(!z.path_exists());
    assert_eq!(z.to_next_sibling_byte(), Some(b'b'));
    assert_eq!(z.path(), b"ab");
}
#[test] fn b1_to_next_k_path_from_missing_path_between_key0_and_descendant_key1() {
    let m: PathMap<()> = [&b"a"[..], b"abcd"].into_iter().collect();
    let mut z = m.read_zipper();
    z.descend_to(b"aa");
    assert!(z.to_next_k_path(1));
    assert_eq!(z.path(), b"ab");
}
#[test] fn b1_to_next_step_from_missing_path_below_child_node() {
    let m: PathMap<()> = [&[0u8,0,1,3,0,3][..], &[0,0,1,3,0,3,1,3,1,2,1]].into_iter().collect();
    let mut z = m.read_zipper();
    z.descend_to(&[0,0,1,3,0,3,1,1]);
    assert!(z.to_next_k_path(5));
    assert_eq!(z.path(), &[0,0,1,3,0,3,1,3]);
}
#[test] fn b1_rooted_exhausted_then_descend_to_nonexistent_then_to_next_step() {
    let m: PathMap<()> = [&[2u8,0][..], &[2,0,1,3,2,3,4,2,5]].into_iter().collect();
    let mut z = m.into_read_zipper(&[2,0,1]);
    assert!(z.descend_last_path());
    assert!(!z.to_next_val()); assert!(z.at_root());
    z.descend_to(&[0]);
    assert!(z.to_next_step()); assert_eq!(z.path(), &[3]);
}

// ---- Bug 2: k_path_internal base-prefix-mismatch exit leaves a stale token
#[test] fn b2_base_mismatch_exit_then_to_next_val() {
    let m: PathMap<()> = [&[0u8, 0, 0, 0, 0, 0, 1][..], &[2]].into_iter().collect();
    let mut z = m.read_zipper();
    assert!(z.to_next_val());
    assert!(!z.to_next_k_path(2));
    assert_eq!(z.path(), &[0, 0, 0, 0, 0]);
    assert!(z.to_next_val());
    assert_eq!(z.path(), &[0, 0, 0, 0, 0, 0, 1]);
}
#[test] fn b2_base_mismatch_exit_then_descend_first_byte() {
    let m: PathMap<()> = [&[0u8, 0, 0, 0, 0, 0, 1][..], &[2]].into_iter().collect();
    let mut z = m.read_zipper();
    assert!(z.to_next_val());
    assert!(!z.to_next_k_path(2));
    assert_eq!(z.descend_first_byte(), Some(0));
}
#[test] fn b2_rooted_failed_descend_first_k_path_then_descend_first_byte() {
    let m: PathMap<()> = [&[2u8,1,3,1,3][..], &[2,5,5]].into_iter().collect();
    let mut z = m.read_zipper_at_path(&[2,1]);
    assert!(!z.descend_first_k_path(4));
    assert_eq!(z.descend_first_byte(), Some(3));
}
#[test] fn b2_interior_focus_failed_k_path_then_to_next_val() {
    let m: PathMap<()> = [&b"ab"[..], b"wxyz"].into_iter().collect();
    let mut z = m.read_zipper();
    z.descend_to(b"a");
    assert!(z.descend_first_k_path(1));
    assert!(!z.to_next_k_path(1));
    assert_eq!(z.path(), b"a");
    assert!(z.to_next_val());
    assert_eq!(z.path(), b"ab");
}

// ---- Bug 3: to_next_get_val origin-prefix-mismatch exit leaves a stale token
#[test] fn b3_rooted_exhausted_to_next_val_then_descend_first_byte() {
    let m: PathMap<()> = [&[1u8,2,3][..], &[1,5]].into_iter().collect();
    let mut z = m.read_zipper_at_path(&[1,2]);
    assert!(z.to_next_val()); assert_eq!(z.path(), &[3]);
    assert!(!z.to_next_val()); assert!(z.at_root());
    assert_eq!(z.descend_first_byte(), Some(3));
}
#[test] fn b3_rooted_exhausted_to_next_val_then_to_next_step() {
    let m: PathMap<()> = [&[1u8,2,3][..], &[1,5]].into_iter().collect();
    let mut z = m.read_zipper_at_path(&[1,2]);
    assert!(z.to_next_val()); assert!(!z.to_next_val());
    assert!(z.to_next_step()); assert_eq!(z.path(), &[3]);
}
#[test] fn b3_rooted_exhausted_to_next_val_then_to_next_val_restarts() {
    let m: PathMap<()> = [&[1u8,2,3][..], &[1,5]].into_iter().collect();
    let mut z = m.read_zipper_at_path(&[1,2]);
    assert!(z.to_next_val()); assert!(!z.to_next_val());
    assert!(z.to_next_val()); assert_eq!(z.path(), &[3]);
}
#[test] fn b3_rooted_descend_first_byte_exhaust_then_restart() {
    let m: PathMap<()> = [&[1u8,1,3,1,3,0][..], &[1,3,4,0,5]].into_iter().collect();
    let mut z = m.read_zipper_at_path(&[1,1,3,1,3]);
    assert_eq!(z.descend_first_byte(), Some(0));
    assert!(!z.to_next_val()); assert!(z.at_root());
    assert!(z.to_next_val()); assert_eq!(z.path(), &[0]);
}

// ---- Bug 4 (pre-existing): DenseByteNode prev-sibling across mask words / from a missing byte
#[test] fn b4_prev_sibling_across_mask_word_boundary() {
    let m: PathMap<()> = [&[10u8][..], &[20], &[70]].into_iter().collect();
    let mut z = m.read_zipper();
    z.descend_to(&[70]);
    assert_eq!(z.to_prev_sibling_byte(), Some(20));
}
#[test] fn b4_prev_sibling_across_two_words() {
    let m: PathMap<()> = [&[10u8][..], &[60], &[200]].into_iter().collect();
    let mut z = m.read_zipper();
    z.descend_to(&[200]);
    assert_eq!(z.to_prev_sibling_byte(), Some(60));
}
#[test] fn b4_dense_prev_sibling_from_nonexistent_byte() {
    let m: PathMap<()> = [&[241u8,192][..], &[247,241,116], &[254,251]].into_iter().collect();
    let mut z = m.read_zipper();
    z.descend_to_byte(60);
    assert_eq!(z.to_prev_sibling_byte(), None);
    z.reset(); z.descend_to_byte(250);
    assert_eq!(z.to_prev_sibling_byte(), Some(247));
}
#[test] fn b5_linelist_prev_sibling_from_nonexistent_byte_after_only_key() {
    let m: PathMap<()> = [&[108u8,142,64][..]].into_iter().collect();
    let mut z = m.read_zipper();
    z.descend_to(&[229]);
    assert_eq!(z.to_prev_sibling_byte(), Some(108));
}
#[test] fn b5_linelist_next_sibling_from_nonexistent_byte_before_only_key() {
    let m: PathMap<()> = [&[108u8,142,64][..]].into_iter().collect();
    let mut z = m.read_zipper();
    z.descend_to(&[5]);
    assert_eq!(z.to_next_sibling_byte(), Some(108));
}
#[test] fn b5_linelist_prev_sibling_from_nonexistent_between_two_keys() {
    let m: PathMap<()> = [&[10u8,1][..], &[200,1]].into_iter().collect();
    let mut z = m.read_zipper();
    z.descend_to(&[100]);
    assert_eq!(z.to_prev_sibling_byte(), Some(10));
    z.reset(); z.descend_to(&[250]);
    assert_eq!(z.to_prev_sibling_byte(), Some(200));
}

// ---- Bug 6: ascent family underflowed excess_key_len on an unprepared path buffer (fork / borrowed path)
#[test] fn b6_fork_root_ascend_byte_is_false_and_to_next_step_terminates() {
    let mut m = PathMap::<u64>::new(); m.set_val_at(&[0u8,0,2,3,0], 138); m.create_path(&[0u8,3]);
    let rz = m.read_zipper_at_path(&[0u8,3]);
    let mut f = rz.fork_read_zipper();
    assert!(!f.ascend_byte());
    assert!(f.at_root());
    let mut f = rz.fork_read_zipper();
    assert!(!f.to_next_step());            // PR head: never returns
    let mut m2 = PathMap::<u64>::new(); m2.set_val_at(&[3u8,3,3], 144); m2.set_val_at(&[1u8], 1);
    let rz2 = m2.read_zipper_at_path(&[3u8,3,3]);
    let mut f2 = rz2.fork_read_zipper();
    assert_eq!(f2.ascend(3), 0);
    assert_eq!(f2.ascend_until(), 0);
    assert!(!f2.to_next_step());
}
#[test] fn b6_borrowed_path_root_ascend_byte_is_false() {
    let mut m = PathMap::<u64>::new(); m.set_val_at(&[0u8,0,2,3,0], 138); m.create_path(&[0u8,3]);
    let p = [0u8, 3];
    let mut z = m.read_zipper_at_borrowed_path(&p);
    assert!(!z.ascend_byte());
    let mut z = m.read_zipper_at_borrowed_path(&p);
    assert!(!z.to_next_step());
    let mut z = m.read_zipper_at_borrowed_path(&p);
    assert_eq!(z.to_prev_sibling_byte(), None);
    assert!(!z.ascend_byte());
}

// ---- Bug 7: EmptyNode::iter_token_for_path returned an exact token for nonexistent keys
#[test] fn b7_empty_node_below_dangling_path_descend_then_ascend() {
    let mut m = PathMap::<u64>::new(); m.set_val_at(&[0u8,0,2], 1); m.create_path(&[0u8,3]);
    let mut z = m.read_zipper_at_path(&[0u8,3]);
    z.descend_to(&[1u8]);
    assert!(!z.path_exists());
    assert_eq!(z.descend_first_byte(), None);
    assert!(z.ascend_byte());              // PR head: unreachable!() in EmptyNode::ascend_iter_token
    assert!(z.at_root());
    assert!(!z.to_next_step());
}
