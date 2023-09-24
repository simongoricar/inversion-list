#![allow(clippy::len_zero)]

use inversion_list::InversionMap;
use test_utilities::TestResult;



#[test]
pub fn continious_inversion_map() -> TestResult {
    let mut map = InversionMap::<u8, ()>::new();

    assert!(map.is_empty());
    assert_eq!(map.len(), 0);

    map.insert(0..=20, ())?;

    assert!(!map.is_empty());
    assert_eq!(map.len(), 1);

    map.insert(0..5, ())?;
    map.insert(5..7, ())?;

    assert!(!map.is_empty());
    assert_eq!(map.len(), 3);

    map.insert(1..3, ())?;

    assert_eq!(map.len(), 5);

    map.insert(14..16, ())?;
    map.insert(12..18, ())?;

    assert_eq!(map.len(), 6);

    Ok(())
}


#[test]
pub fn non_continious_inversion_map() -> TestResult {
    let mut map = InversionMap::<u8, ()>::new();

    map.insert(0..10, ())?;
    map.insert(15..18, ())?;

    assert_eq!(map.len(), 2);

    Ok(())
}
