use hashbrown::hash_map as base;

use crate::hash_map::base::{RawVacantEntryMut, RawOccupiedEntryMut, RawEntryMut};
use crate::hash_map::Entry::{Occupied, Vacant};
use std::borrow::Borrow;
use std::error::Error;
use std::fmt::{self, Debug};
use std::hash::{BuildHasher, Hash, RandomState};
use std::iter::FusedIterator;
use std::ops::Index;

/// A [hash map] implemented with quadratic probing and SIMD lookup.
///
/// By default, `HashMap` uses a hashing algorithm selected to provide
/// resistance against HashDoS attacks. The algorithm is randomly seeded, and a
/// reasonable best-effort is made to generate this seed from a high quality,
/// secure source of randomness provided by the host without blocking the
/// program. Because of this, the randomness of the seed depends on the output
/// quality of the system's random number coroutine when the seed is created.
/// In particular, seeds generated when the system's entropy pool is abnormally
/// low such as during system boot may be of a lower quality.
///
/// The default hashing algorithm is currently SipHash 1-3, though this is
/// subject to change at any point in the future. While its performance is very
/// competitive for medium sized keys, other hashing algorithms will outperform
/// it for small keys such as integers as well as large keys such as long
/// strings, though those algorithms will typically *not* protect against
/// attacks such as HashDoS.
///
/// The hashing algorithm can be replaced on a per-`HashMap` basis using the
/// [`default`], [`with_hasher`], and [`with_capacity_and_hasher`] methods.
/// There are many alternative [hashing algorithms available on crates.io].
///
/// It is required that the keys implement the [`Eq`] and [`Hash`] traits, although
/// this can frequently be achieved by using `#[derive(PartialEq, Eq, Hash)]`.
/// If you implement these yourself, it is important that the following
/// property holds:
///
/// ```text
/// k1 == k2 -> hash(k1) == hash(k2)
/// ```
///
/// In other words, if two keys are equal, their hashes must be equal.
/// Violating this property is a logic error.
///
/// It is also a logic error for a key to be modified in such a way that the key's
/// hash, as determined by the [`Hash`] trait, or its equality, as determined by
/// the [`Eq`] trait, changes while it is in the map. This is normally only
/// possible through [`Cell`], [`RefCell`], global state, I/O, or unsafe code.
///
/// The behavior resulting from either logic error is not specified, but will
/// be encapsulated to the `HashMap` that observed the logic error and not
/// result in undefined behavior. This could include panics, incorrect results,
/// aborts, memory leaks, and non-termination.
///
/// The hash table implementation is a Rust port of Google's [SwissTable].
/// The original C++ version of SwissTable can be found [here], and this
/// [CppCon talk] gives an overview of how the algorithm works.
///
/// [hash map]: crate::collections#use-a-hashmap-when
/// [hashing algorithms available on crates.io]: https://crates.io/keywords/hasher
/// [SwissTable]: https://abseil.io/blog/20180927-swisstables
/// [here]: https://github.com/abseil/abseil-cpp/blob/master/absl/container/internal/raw_hash_set.h
/// [CppCon talk]: https://www.youtube.com/watch?v=ncHmEUmJZf4
///
/// # Examples
///
/// ```
/// use std::collections::HashMap;
///
/// // Type inference lets us omit an explicit type signature (which
/// // would be `HashMap<String, String>` in this example).
/// let mut book_reviews = HashMap::new();
///
/// // Review some books.
/// book_reviews.insert(
///     "Adventures of Huckleberry Finn".to_string(),
///     "My favorite book.".to_string(),
/// );
/// book_reviews.insert(
///     "Grimms' Fairy Tales".to_string(),
///     "Masterpiece.".to_string(),
/// );
/// book_reviews.insert(
///     "Pride and Prejudice".to_string(),
///     "Very enjoyable.".to_string(),
/// );
/// book_reviews.insert(
///     "The Adventures of Sherlock Holmes".to_string(),
///     "Eye lyked it alot.".to_string(),
/// );
///
/// // Check for a specific one.
/// // When collections store owned values (String), they can still be
/// // queried using references (&str).
/// if !book_reviews.contains_key("Les Misérables") {
///     println!("We've got {} reviews, but Les Misérables ain't one.",
///              book_reviews.len());
/// }
///
/// // oops, this review has a lot of spelling mistakes, let's delete it.
/// book_reviews.remove("The Adventures of Sherlock Holmes");
///
/// // Look up the values associated with some keys.
/// let to_find = ["Pride and Prejudice", "Alice's Adventure in Wonderland"];
/// for &book in &to_find {
///     match book_reviews.get(book) {
///         Some(review) => println!("{book}: {review}"),
///         None => println!("{book} is unreviewed.")
///     }
/// }
///
/// // Look up the value for a key (will panic if the key is not found).
/// println!("Review for Jane: {}", book_reviews["Pride and Prejudice"]);
///
/// // Iterate over everything.
/// for (book, review) in &book_reviews {
///     println!("{book}: \"{review}\"");
/// }
/// ```
///
/// A `HashMap` with a known list of items can be initialized from an array:
///
/// ```
/// use std::collections::HashMap;
///
/// let solar_distance = HashMap::from([
///     ("Mercury", 0.4),
///     ("Venus", 0.7),
///     ("Earth", 1.0),
///     ("Mars", 1.5),
/// ]);
/// ```
///
/// `HashMap` implements an [`Entry` API](#method.entry), which allows
/// for complex methods of getting, setting, updating and removing keys and
/// their values:
///
/// ```
/// use std::collections::HashMap;
///
/// // type inference lets us omit an explicit type signature (which
/// // would be `HashMap<&str, u8>` in this example).
/// let mut player_stats = HashMap::new();
///
/// fn random_stat_buff() -> u8 {
///     // could actually return some random value here - let's just return
///     // some fixed value for now
///     42
/// }
///
/// // insert a key only if it doesn't already exist
/// player_stats.entry("health").or_insert(100);
///
/// // insert a key using a function that provides a new value only if it
/// // doesn't already exist
/// player_stats.entry("defence").or_insert_with(random_stat_buff);
///
/// // update a key, guarding against the key possibly not being set
/// let stat = player_stats.entry("attack").or_insert(100);
/// *stat += random_stat_buff();
///
/// // modify an entry before an insert with in-place mutation
/// player_stats.entry("mana").and_modify(|mana| *mana += 200).or_insert(100);
/// ```
///
/// The easiest way to use `HashMap` with a custom key type is to derive [`Eq`] and [`Hash`].
/// We must also derive [`PartialEq`].
///
/// [`RefCell`]: crate::cell::RefCell
/// [`Cell`]: crate::cell::Cell
/// [`default`]: Default::default
/// [`with_hasher`]: Self::with_hasher
/// [`with_capacity_and_hasher`]: Self::with_capacity_and_hasher
///
/// ```
/// use std::collections::HashMap;
///
/// #[derive(Hash, Eq, PartialEq, Debug)]
/// struct Viking {
///     name: String,
///     country: String,
/// }
///
/// impl Viking {
///     /// Creates a new Viking.
///     fn new(name: &str, country: &str) -> Viking {
///         Viking { name: name.to_string(), country: country.to_string() }
///     }
/// }
///
/// // Use a HashMap to store the vikings' health points.
/// let vikings = HashMap::from([
///     (Viking::new("Einar", "Norway"), 25),
///     (Viking::new("Olaf", "Denmark"), 24),
///     (Viking::new("Harald", "Iceland"), 12),
/// ]);
///
/// // Use derived implementation to print the status of the vikings.
/// for (viking, health) in &vikings {
///     println!("{viking:?} has {health} hp");
/// }
/// ```

pub struct HashMap<K, V, S = RandomState> {
    base: base::HashMap<K, V, S>,
}

impl<K, V> HashMap<K, V, RandomState> {
    /// Creates an empty `HashMap`.
    ///
    /// The hash map is initially created with a capacity of 0, so it will not allocate until it
    /// is first inserted into.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// let mut map: HashMap<&str, i32> = HashMap::new();
    /// ```
    #[inline]
    #[must_use]
    pub fn new() -> HashMap<K, V, RandomState> {
        Default::default()
    }

    /// Creates an empty `HashMap` with at least the specified capacity.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is 0, the hash map will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// let mut map: HashMap<&str, i32> = HashMap::with_capacity(10);
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> HashMap<K, V, RandomState> {
        HashMap::with_capacity_and_hasher(capacity, Default::default())
    }
}

impl<K, V, S> HashMap<K, V, S> {
    /// Creates an empty `HashMap` which will use the given hash builder to hash
    /// keys.
    ///
    /// The created map has the default initial capacity.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and
    /// is designed to allow HashMaps to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for
    /// the HashMap to be useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::hash::RandomState;
    ///
    /// let s = RandomState::new();
    /// let mut map = HashMap::with_hasher(s);
    /// map.insert(1, 2);
    /// ```
    #[inline]
    pub const fn with_hasher(hash_builder: S) -> HashMap<K, V, S> {
        HashMap { base: base::HashMap::with_hasher(hash_builder) }
    }

    /// Creates an empty `HashMap` with at least the specified capacity, using
    /// `hasher` to hash the keys.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is 0, the hash map will not allocate.
    ///
    /// Warning: `hasher` is normally randomly generated, and
    /// is designed to allow HashMaps to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// The `hasher` passed should implement the [`BuildHasher`] trait for
    /// the HashMap to be useful, see its documentation for details.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::hash::RandomState;
    ///
    /// let s = RandomState::new();
    /// let mut map = HashMap::with_capacity_and_hasher(10, s);
    /// map.insert(1, 2);
    /// ```
    #[inline]
    pub fn with_capacity_and_hasher(capacity: usize, hasher: S) -> HashMap<K, V, S> {
        HashMap { base: base::HashMap::with_capacity_and_hasher(capacity, hasher) }
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the `HashMap<K, V>` might be able to hold
    /// more, but is guaranteed to be able to hold at least this many.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// let map: HashMap<i32, i32> = HashMap::with_capacity(100);
    /// assert!(map.capacity() >= 100);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.base.capacity()
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for key in map.keys() {
    ///     println!("{key}");
    /// }
    /// ```
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over keys takes O(capacity) time
    /// instead of O(len) because it internally visits empty buckets too.
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { inner: self.iter() }
    }

    /// Creates a consuming iterator visiting all the keys in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// let mut vec: Vec<&str> = map.into_keys().collect();
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// ```
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over keys takes O(capacity) time
    /// instead of O(len) because it internally visits empty buckets too.
    #[inline]
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys { inner: self.into_iter() }
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for val in map.values() {
    ///     println!("{val}");
    /// }
    /// ```
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over values takes O(capacity) time
    /// instead of O(len) because it internally visits empty buckets too.
    pub fn values(&self) -> Values<'_, K, V> {
        Values { inner: self.iter() }
    }

    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for val in map.values_mut() {
    ///     *val = *val + 10;
    /// }
    ///
    /// for val in map.values() {
    ///     println!("{val}");
    /// }
    /// ```
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over values takes O(capacity) time
    /// instead of O(len) because it internally visits empty buckets too.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut { inner: self.iter_mut() }
    }

    /// Creates a consuming iterator visiting all the values in arbitrary order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// let mut vec: Vec<i32> = map.into_values().collect();
    /// // The `IntoValues` iterator produces values in arbitrary order, so
    /// // the values must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over values takes O(capacity) time
    /// instead of O(len) because it internally visits empty buckets too.
    #[inline]
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues { inner: self.into_iter() }
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {key} val: {val}");
    /// }
    /// ```
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over map takes O(capacity) time
    /// instead of O(len) because it internally visits empty buckets too.
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter { base: self.base.iter() }
    }

    /// An iterator visiting all key-value pairs in arbitrary order,
    /// with mutable references to the values.
    /// The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// // Update all values
    /// for (_, val) in map.iter_mut() {
    ///     *val *= 2;
    /// }
    ///
    /// for (key, val) in &map {
    ///     println!("key: {key} val: {val}");
    /// }
    /// ```
    ///
    /// # Performance
    ///
    /// In the current implementation, iterating over map takes O(capacity) time
    /// instead of O(len) because it internally visits empty buckets too.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut { base: self.base.iter_mut() }
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut a = HashMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.base.len()
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut a = HashMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Clears the map, returning all key-value pairs as an iterator. Keeps the
    /// allocated memory for reuse.
    ///
    /// If the returned iterator is dropped before being fully consumed, it
    /// drops the remaining key-value pairs. The returned iterator keeps a
    /// mutable borrow on the map to optimize its implementation.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut a = HashMap::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    ///
    /// for (k, v) in a.drain().take(1) {
    ///     assert!(k == 1 || k == 2);
    ///     assert!(v == "a" || v == "b");
    /// }
    ///
    /// assert!(a.is_empty());
    /// ```
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, K, V> {
        Drain { base: self.base.drain() }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)` returns `false`.
    /// The elements are visited in unsorted (and unspecified) order.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map: HashMap<i32, i32> = (0..8).map(|x| (x, x*10)).collect();
    /// map.retain(|&k, _| k % 2 == 0);
    /// assert_eq!(map.len(), 4);
    /// ```
    ///
    /// # Performance
    ///
    /// In the current implementation, this operation takes O(capacity) time
    /// instead of O(len) because it internally visits empty buckets too.
    #[inline]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        self.base.retain(f)
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut a = HashMap::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.base.clear();
    }

    /// Returns a reference to the map's [`BuildHasher`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::hash::RandomState;
    ///
    /// let hasher = RandomState::new();
    /// let map: HashMap<i32, i32> = HashMap::with_hasher(hasher);
    /// let hasher: &RandomState = map.hasher();
    /// ```
    #[inline]
    pub fn hasher(&self) -> &S {
        self.base.hasher()
    }
}

impl<K, V, S> HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `HashMap`. The collection may reserve more space to speculatively
    /// avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows [`usize`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// let mut map: HashMap<&str, i32> = HashMap::new();
    /// map.reserve(10);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.base.reserve(additional)
    }

    /// Shrinks the capacity of the map as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map: HashMap<i32, i32> = HashMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.base.shrink_to_fit();
    }

    /// Shrinks the capacity of the map with a lower limit. It will drop
    /// down no lower than the supplied limit while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map: HashMap<i32, i32> = HashMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10);
    /// map.shrink_to(0);
    /// assert!(map.capacity() >= 2);
    /// ```
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.base.shrink_to(min_capacity);
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut letters = HashMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     letters.entry(ch).and_modify(|counter| *counter += 1).or_insert(1);
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    #[inline]
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        map_entry(self.base.entry(key))
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    #[inline]
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.base.get(k)
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    #[inline]
    pub fn get_key_value<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.base.get_key_value(k)
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    #[inline]
    pub fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.base.contains_key(k)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    #[inline]
    pub fn get_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.base.get_mut(k)
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, [`None`] is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [module-level
    /// documentation] for more.
    ///
    /// [module-level documentation]: crate::collections#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    #[inline]
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.base.insert(k, v)
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    #[inline]
    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.base.remove(k)
    }

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// # fn main() {
    /// let mut map = HashMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove(&1), None);
    /// # }
    /// ```
    #[inline]
    pub fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.base.remove_entry(k)
    }
}

impl<K, V, S> Clone for HashMap<K, V, S>
where
    K: Clone,
    V: Clone,
    S: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self { base: self.base.clone() }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.base.clone_from(&source.base);
    }
}

impl<K, V, S> PartialEq for HashMap<K, V, S>
where
    K: Eq + Hash,
    V: PartialEq,
    S: BuildHasher,
{
    fn eq(&self, other: &HashMap<K, V, S>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter().all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V, S> Eq for HashMap<K, V, S>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
}

impl<K, V, S> Debug for HashMap<K, V, S>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V, S> Default for HashMap<K, V, S>
where
    S: Default,
{
    /// Creates an empty `HashMap<K, V, S>`, with the `Default` value for the hasher.
    #[inline]
    fn default() -> HashMap<K, V, S> {
        HashMap::with_hasher(Default::default())
    }
}

impl<K, Q: ?Sized, V, S> Index<&Q> for HashMap<K, V, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash,
    S: BuildHasher,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `HashMap`.
    #[inline]
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

// Note: as what is currently the most convenient built-in way to construct
// a HashMap, a simple usage of this function must not *require* the user
// to provide a type annotation in order to infer the third type parameter
// (the hasher parameter, conventionally "S").
// To that end, this impl is defined using RandomState as the concrete
// type of S, rather than being generic over `S: BuildHasher + Default`.
// It is expected that users who want to specify a hasher will manually use
// `with_capacity_and_hasher`.
// If type parameter defaults worked on impls, and if type parameter
// defaults could be mixed with const generics, then perhaps
// this could be generalized.
// See also the equivalent impl on HashSet.
impl<K, V, const N: usize> From<[(K, V); N]> for HashMap<K, V, RandomState>
where
    K: Eq + Hash,
{
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let map1 = HashMap::from([(1, 2), (3, 4)]);
    /// let map2: HashMap<_, _> = [(1, 2), (3, 4)].into();
    /// assert_eq!(map1, map2);
    /// ```
    fn from(arr: [(K, V); N]) -> Self {
        Self::from_iter(arr)
    }
}

/// An iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`iter`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`iter`]: HashMap::iter
///
/// # Example
///
/// ```
/// use std::collections::HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter = map.iter();
/// ```
pub struct Iter<'a, K: 'a, V: 'a> {
    base: base::Iter<'a, K, V>,
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
impl<K, V> Clone for Iter<'_, K, V> {
    #[inline]
    fn clone(&self) -> Self {
        Iter { base: self.base.clone() }
    }
}

impl<K: Debug, V: Debug> fmt::Debug for Iter<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A mutable iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`iter_mut`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`iter_mut`]: HashMap::iter_mut
///
/// # Example
///
/// ```
/// use std::collections::HashMap;
///
/// let mut map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter = map.iter_mut();
/// ```
pub struct IterMut<'a, K: 'a, V: 'a> {
    base: base::IterMut<'a, K, V>,
}

impl<'a, K, V> IterMut<'a, K, V> {
    /// Returns an iterator of references over the remaining items.
    #[inline]
    pub(super) fn iter(&self) -> Iter<'_, K, V> {
        Iter { base: self.base.iter() }
    }
}

/// An owning iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`into_iter`] method on [`HashMap`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
///
/// # Example
///
/// ```
/// use std::collections::HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter = map.into_iter();
/// ```
pub struct IntoIter<K, V> {
    base: base::IntoIter<K, V>,
}

impl<K, V> IntoIter<K, V> {
    /// Returns an iterator of references over the remaining items.
    #[inline]
    pub(super) fn iter(&self) -> Iter<'_, K, V> {
        Iter { base: self.base.iter() }
    }
}

/// An iterator over the keys of a `HashMap`.
///
/// This `struct` is created by the [`keys`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`keys`]: HashMap::keys
///
/// # Example
///
/// ```
/// use std::collections::HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter_keys = map.keys();
/// ```
pub struct Keys<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
impl<K, V> Clone for Keys<'_, K, V> {
    #[inline]
    fn clone(&self) -> Self {
        Keys { inner: self.inner.clone() }
    }
}

impl<K: Debug, V> fmt::Debug for Keys<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An iterator over the values of a `HashMap`.
///
/// This `struct` is created by the [`values`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`values`]: HashMap::values
///
/// # Example
///
/// ```
/// use std::collections::HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter_values = map.values();
/// ```
pub struct Values<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
impl<K, V> Clone for Values<'_, K, V> {
    #[inline]
    fn clone(&self) -> Self {
        Values { inner: self.inner.clone() }
    }
}

impl<K, V: Debug> fmt::Debug for Values<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A draining iterator over the entries of a `HashMap`.
///
/// This `struct` is created by the [`drain`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`drain`]: HashMap::drain
///
/// # Example
///
/// ```
/// use std::collections::HashMap;
///
/// let mut map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter = map.drain();
/// ```
pub struct Drain<'a, K: 'a, V: 'a> {
    base: base::Drain<'a, K, V>,
}

impl<'a, K, V> Drain<'a, K, V> {
    /// Returns an iterator of references over the remaining items.
    #[inline]
    pub(super) fn iter(&self) -> Iter<'_, K, V> {
        Iter { base: self.base.rustc_iter() }
    }
}

/// A mutable iterator over the values of a `HashMap`.
///
/// This `struct` is created by the [`values_mut`] method on [`HashMap`]. See its
/// documentation for more.
///
/// [`values_mut`]: HashMap::values_mut
///
/// # Example
///
/// ```
/// use std::collections::HashMap;
///
/// let mut map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter_values = map.values_mut();
/// ```
pub struct ValuesMut<'a, K: 'a, V: 'a> {
    inner: IterMut<'a, K, V>,
}

/// An owning iterator over the keys of a `HashMap`.
///
/// This `struct` is created by the [`into_keys`] method on [`HashMap`].
/// See its documentation for more.
///
/// [`into_keys`]: HashMap::into_keys
///
/// # Example
///
/// ```
/// use std::collections::HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter_keys = map.into_keys();
/// ```
pub struct IntoKeys<K, V> {
    inner: IntoIter<K, V>,
}

/// An owning iterator over the values of a `HashMap`.
///
/// This `struct` is created by the [`into_values`] method on [`HashMap`].
/// See its documentation for more.
///
/// [`into_values`]: HashMap::into_values
///
/// # Example
///
/// ```
/// use std::collections::HashMap;
///
/// let map = HashMap::from([
///     ("a", 1),
/// ]);
/// let iter_keys = map.into_values();
/// ```
pub struct IntoValues<K, V> {
    inner: IntoIter<K, V>,
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`HashMap`].
///
/// [`entry`]: HashMap::entry
pub enum Entry<'a, K: 'a, V: 'a> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V>),

    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V>),
}

impl<K: Debug, V: Debug> Debug for Entry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Vacant(ref v) => f.debug_tuple("Entry").field(v).finish(),
            Occupied(ref o) => f.debug_tuple("Entry").field(o).finish(),
        }
    }
}

/// A view into an occupied entry in a `HashMap`.
/// It is part of the [`Entry`] enum.
pub struct OccupiedEntry<'a, K: 'a, V: 'a> {
    base: base::OccupiedEntry<'a, K, V>,
}

impl<K: Debug, V: Debug> Debug for OccupiedEntry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key", self.key())
            .field("value", self.get())
            .finish_non_exhaustive()
    }
}

/// A view into a vacant entry in a `HashMap`.
/// It is part of the [`Entry`] enum.
pub struct VacantEntry<'a, K: 'a, V: 'a> {
    base: base::VacantEntry<'a, K, V>,
}

impl<K: Debug, V> Debug for VacantEntry<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VacantEntry").field(self.key()).finish()
    }
}

impl<'a, K, V, S> IntoIterator for &'a HashMap<K, V, S> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    #[inline]
    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K, V, S> IntoIterator for &'a mut HashMap<K, V, S> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    #[inline]
    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

impl<K, V, S> IntoIterator for HashMap<K, V, S> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    /// Creates a consuming iterator, that is, one that moves each key-value
    /// pair out of the map in arbitrary order. The map cannot be used after
    /// calling this.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let map = HashMap::from([
    ///     ("a", 1),
    ///     ("b", 2),
    ///     ("c", 3),
    /// ]);
    ///
    /// // Not possible with .iter()
    /// let vec: Vec<(&str, i32)> = map.into_iter().collect();
    /// ```
    #[inline]
    fn into_iter(self) -> IntoIter<K, V> {
        IntoIter { base: self.base.into_iter() }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        self.base.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
    #[inline]
    fn count(self) -> usize {
        self.base.len()
    }
    #[inline]
    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.base.fold(init, f)
    }
}
impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.base.len()
    }
}

impl<K, V> FusedIterator for Iter<'_, K, V> {}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        self.base.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
    #[inline]
    fn count(self) -> usize {
        self.base.len()
    }
    #[inline]
    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.base.fold(init, f)
    }
}
impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.base.len()
    }
}
impl<K, V> FusedIterator for IterMut<'_, K, V> {}

impl<K, V> fmt::Debug for IterMut<'_, K, V>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<(K, V)> {
        self.base.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
    #[inline]
    fn count(self) -> usize {
        self.base.len()
    }
    #[inline]
    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.base.fold(init, f)
    }
}
impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.base.len()
    }
}
impl<K, V> FusedIterator for IntoIter<K, V> {}

impl<K: Debug, V: Debug> fmt::Debug for IntoIter<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline]
    fn next(&mut self) -> Option<&'a K> {
        self.inner.next().map(|(k, _)| k)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[inline]
    fn count(self) -> usize {
        self.inner.len()
    }
    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (k, _)| f(acc, k))
    }
}
impl<K, V> ExactSizeIterator for Keys<'_, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for Keys<'_, K, V> {}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<&'a V> {
        self.inner.next().map(|(_, v)| v)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[inline]
    fn count(self) -> usize {
        self.inner.len()
    }
    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (_, v)| f(acc, v))
    }
}
impl<K, V> ExactSizeIterator for Values<'_, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for Values<'_, K, V> {}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<&'a mut V> {
        self.inner.next().map(|(_, v)| v)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[inline]
    fn count(self) -> usize {
        self.inner.len()
    }
    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (_, v)| f(acc, v))
    }
}
impl<K, V> ExactSizeIterator for ValuesMut<'_, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for ValuesMut<'_, K, V> {}

impl<K, V: fmt::Debug> fmt::Debug for ValuesMut<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.iter().map(|(_, val)| val)).finish()
    }
}

impl<K, V> Iterator for IntoKeys<K, V> {
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<K> {
        self.inner.next().map(|(k, _)| k)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[inline]
    fn count(self) -> usize {
        self.inner.len()
    }
    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (k, _)| f(acc, k))
    }
}
impl<K, V> ExactSizeIterator for IntoKeys<K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for IntoKeys<K, V> {}

impl<K: Debug, V> fmt::Debug for IntoKeys<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.iter().map(|(k, _)| k)).finish()
    }
}

impl<K, V> Iterator for IntoValues<K, V> {
    type Item = V;

    #[inline]
    fn next(&mut self) -> Option<V> {
        self.inner.next().map(|(_, v)| v)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
    #[inline]
    fn count(self) -> usize {
        self.inner.len()
    }
    #[inline]
    fn fold<B, F>(self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.inner.fold(init, |acc, (_, v)| f(acc, v))
    }
}
impl<K, V> ExactSizeIterator for IntoValues<K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<K, V> FusedIterator for IntoValues<K, V> {}

impl<K, V: Debug> fmt::Debug for IntoValues<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.inner.iter().map(|(_, v)| v)).finish()
    }
}

impl<'a, K, V> Iterator for Drain<'a, K, V> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<(K, V)> {
        self.base.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.base.size_hint()
    }
    #[inline]
    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.base.fold(init, f)
    }
}
impl<K, V> ExactSizeIterator for Drain<'_, K, V> {
    #[inline]
    fn len(&self) -> usize {
        self.base.len()
    }
}
impl<K, V> FusedIterator for Drain<'_, K, V> {}

impl<K, V> fmt::Debug for Drain<'_, K, V>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'a, K, V> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// map.entry("poneyland").or_insert(3);
    /// assert_eq!(map["poneyland"], 3);
    ///
    /// *map.entry("poneyland").or_insert(10) *= 2;
    /// assert_eq!(map["poneyland"], 6);
    /// ```
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// let value = "hoho";
    ///
    /// map.entry("poneyland").or_insert_with(|| value);
    ///
    /// assert_eq!(map["poneyland"], "hoho");
    /// ```
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    /// This method allows for generating key-derived values for insertion by providing the default
    /// function a reference to the key that was moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying the key is
    /// unnecessary, unlike with `.or_insert_with(|| ... )`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map: HashMap<&str, usize> = HashMap::new();
    ///
    /// map.entry("poneyland").or_insert_with_key(|key| key.chars().count());
    ///
    /// assert_eq!(map["poneyland"], 9);
    /// ```
    #[inline]
    pub fn or_insert_with_key<F: FnOnce(&K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    #[inline]
    pub fn key(&self) -> &K {
        match *self {
            Occupied(ref entry) => entry.key(),
            Vacant(ref entry) => entry.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 42);
    ///
    /// map.entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 43);
    /// ```
    #[inline]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Occupied(mut entry) => {
                f(entry.get_mut());
                Occupied(entry)
            }
            Vacant(entry) => Vacant(entry),
        }
    }
}

impl<'a, K, V: Default> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() {
    /// use std::collections::HashMap;
    ///
    /// let mut map: HashMap<&str, Option<u32>> = HashMap::new();
    /// map.entry("poneyland").or_default();
    ///
    /// assert_eq!(map["poneyland"], None);
    /// # }
    /// ```
    #[inline]
    pub fn or_default(self) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(Default::default()),
        }
    }
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    #[inline]
    pub fn key(&self) -> &K {
        self.base.key()
    }

    /// Take the ownership of the key and value from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::collections::hash_map::Entry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     // We delete the entry from the map.
    ///     o.remove_entry();
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// ```
    #[inline]
    pub fn remove_entry(self) -> (K, V) {
        self.base.remove_entry()
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::collections::hash_map::Entry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.get(), &12);
    /// }
    /// ```
    #[inline]
    pub fn get(&self) -> &V {
        self.base.get()
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: Self::into_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::collections::hash_map::Entry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(*o.get(), 22);
    ///
    ///     // We can use the same Entry multiple times.
    ///     *o.get_mut() += 2;
    /// }
    ///
    /// assert_eq!(map["poneyland"], 24);
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        self.base.get_mut()
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: Self::get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::collections::hash_map::Entry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     *o.into_mut() += 10;
    /// }
    ///
    /// assert_eq!(map["poneyland"], 22);
    /// ```
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        self.base.into_mut()
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::collections::hash_map::Entry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(mut o) = map.entry("poneyland") {
    ///     assert_eq!(o.insert(15), 12);
    /// }
    ///
    /// assert_eq!(map["poneyland"], 15);
    /// ```
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        self.base.insert(value)
    }

    /// Takes the value out of the entry, and returns it.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::collections::hash_map::Entry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.entry("poneyland").or_insert(12);
    ///
    /// if let Entry::Occupied(o) = map.entry("poneyland") {
    ///     assert_eq!(o.remove(), 12);
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// ```
    #[inline]
    pub fn remove(self) -> V {
        self.base.remove()
    }
}

impl<'a, K: 'a, V: 'a> VacantEntry<'a, K, V> {
    /// Gets a reference to the key that would be used when inserting a value
    /// through the `VacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// assert_eq!(map.entry("poneyland").key(), &"poneyland");
    /// ```
    #[inline]
    pub fn key(&self) -> &K {
        self.base.key()
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::collections::hash_map::Entry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// if let Entry::Vacant(v) = map.entry("poneyland") {
    ///     v.into_key();
    /// }
    /// ```
    #[inline]
    pub fn into_key(self) -> K {
        self.base.into_key()
    }

    /// Sets the value of the entry with the `VacantEntry`'s key,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashMap;
    /// use std::collections::hash_map::Entry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// if let Entry::Vacant(o) = map.entry("poneyland") {
    ///     o.insert(37);
    /// }
    /// assert_eq!(map["poneyland"], 37);
    /// ```
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        self.base.insert(value)
    }
}

impl<K, V, S> FromIterator<(K, V)> for HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> HashMap<K, V, S> {
        let mut map = HashMap::with_hasher(Default::default());
        map.extend(iter);
        map
    }
}

/// Inserts all new key-values from the iterator and replaces values with existing
/// keys with new values returned from the iterator.
impl<K, V, S> Extend<(K, V)> for HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        self.base.extend(iter)
    }
}

impl<'a, K, V, S> Extend<(&'a K, &'a V)> for HashMap<K, V, S>
where
    K: Eq + Hash + Copy,
    V: Copy,
    S: BuildHasher,
{
    #[inline]
    fn extend<T: IntoIterator<Item = (&'a K, &'a V)>>(&mut self, iter: T) {
        self.base.extend(iter)
    }
}

#[inline]
fn map_entry<'a, K: 'a, V: 'a, S: 'a>(raw: base::Entry<'a, K, V, S>) -> Entry<'a, K, V> {
    match raw {
        base::Entry::Occupied(base) => Entry::Occupied(OccupiedEntry { base }),
        base::Entry::Vacant(base) => Entry::Vacant(VacantEntry { base }),
    }
}

#[inline]
fn map_raw_entry<'a, K: 'a, V: 'a, S: 'a>(
    raw: base::RawEntryMut<'a, K, V, S>,
) -> RawEntryMut<'a, K, V, S> {
    match raw {
        base::RawEntryMut::Occupied(base) => RawEntryMut::Occupied(RawOccupiedEntryMut { base }),
        base::RawEntryMut::Vacant(base) => RawEntryMut::Vacant(RawVacantEntryMut { base }),
    }
}

#[allow(dead_code)]
fn assert_covariance() {
    fn map_key<'new>(v: HashMap<&'static str, u8>) -> HashMap<&'new str, u8> {
        v
    }
    fn map_val<'new>(v: HashMap<u8, &'static str>) -> HashMap<u8, &'new str> {
        v
    }
    fn iter_key<'a, 'new>(v: Iter<'a, &'static str, u8>) -> Iter<'a, &'new str, u8> {
        v
    }
    fn iter_val<'a, 'new>(v: Iter<'a, u8, &'static str>) -> Iter<'a, u8, &'new str> {
        v
    }
    fn into_iter_key<'new>(v: IntoIter<&'static str, u8>) -> IntoIter<&'new str, u8> {
        v
    }
    fn into_iter_val<'new>(v: IntoIter<u8, &'static str>) -> IntoIter<u8, &'new str> {
        v
    }
    fn keys_key<'a, 'new>(v: Keys<'a, &'static str, u8>) -> Keys<'a, &'new str, u8> {
        v
    }
    fn keys_val<'a, 'new>(v: Keys<'a, u8, &'static str>) -> Keys<'a, u8, &'new str> {
        v
    }
    fn values_key<'a, 'new>(v: Values<'a, &'static str, u8>) -> Values<'a, &'new str, u8> {
        v
    }
    fn values_val<'a, 'new>(v: Values<'a, u8, &'static str>) -> Values<'a, u8, &'new str> {
        v
    }
    fn drain<'new>(
        d: Drain<'static, &'static str, &'static str>,
    ) -> Drain<'new, &'new str, &'new str> {
        d
    }
}
