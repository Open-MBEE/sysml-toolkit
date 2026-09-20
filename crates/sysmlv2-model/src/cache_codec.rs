//! Private schema-directed binary encoding for build-versioned library caches.
//! Fixed record layouts omit redundant collection headers. Scalar tags retain
//! dynamic JSON number types. String/byte lengths and collection counts are bounded.
#[cfg(test)]
use serde::Deserialize;
use serde::{
    Serialize,
    de::{
        self, DeserializeOwned, DeserializeSeed, EnumAccess, IntoDeserializer, MapAccess,
        SeqAccess, VariantAccess, Visitor,
    },
    ser,
};
use std::fmt;

#[derive(Debug)]
pub(crate) struct Error(String);
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
impl std::error::Error for Error {}
impl ser::Error for Error {
    fn custom<T: fmt::Display>(s: T) -> Self {
        Self(s.to_string())
    }
}
impl de::Error for Error {
    fn custom<T: fmt::Display>(s: T) -> Self {
        Self(s.to_string())
    }
}
type Result<T> = std::result::Result<T, Error>;
#[cold]
fn bad() -> Error {
    Error("invalid prepared-library encoding".into())
}
const UNIT: u8 = 0;
const FALSE: u8 = 1;
const TRUE: u8 = 2;
const UINT: u8 = 3;
const INT: u8 = 4;
const FLOAT: u8 = 5;
const STR: u8 = 6;
const SEQ: u8 = 7;
const MAP: u8 = 8;
const ENUM: u8 = 9;
const SOME: u8 = 10;
const BYTES: u8 = 11;
pub(crate) fn encode(value: &impl Serialize) -> Result<Vec<u8>> {
    let mut w = Writer::default();
    value.serialize(&mut w)?;
    let mut out = Writer::default();
    out.count(w.2.len() as u64);
    for value in &w.2 {
        out.count(value.len() as u64);
        out.0.extend_from_slice(value.as_bytes());
    }
    out.0.extend(w.0);
    Ok(out.0)
}
pub(crate) fn decode<T: DeserializeOwned>(bytes: &[u8]) -> Result<T> {
    let _strings = SharedStrings::enter();
    let mut r = Reader {
        bytes,
        depth: 0,
        strings: Vec::new(),
    };
    let count = r.length()?;
    if count > 1_048_576 {
        return Err(bad());
    }
    for _ in 0..count {
        let len = r.length()?;
        let text = std::str::from_utf8(r.take(len)?).map_err(|_| bad())?;
        r.strings.push(text);
    }
    let value = T::deserialize(&mut r)?;
    if !r.bytes.is_empty() {
        return Err(bad());
    }
    Ok(value)
}
#[derive(Default)]
struct Writer(
    Vec<u8>,
    std::collections::HashMap<std::sync::Arc<str>, u64>,
    Vec<std::sync::Arc<str>>,
);
impl Writer {
    #[inline]
    fn count(&mut self, mut n: u64) {
        while n >= 128 {
            self.0.push(n as u8 | 128);
            n >>= 7;
        }
        self.0.push(n as u8);
    }
    fn collection(&mut self, tag: u8, n: usize) {
        self.0.push(tag);
        self.count(n as u64);
    }
    fn variant(&mut self, n: u32) {
        self.0.push(ENUM);
        self.count(n as u64);
    }
}
struct Compound<'a>(&'a mut Writer);
macro_rules! integer_ser { ($($name:ident:$ty:ty => $dest:ident),*) => { $(fn $name(self,v:$ty)->Result<()> { self.$dest(v as _) })* }; }
impl<'a> ser::Serializer for &'a mut Writer {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Compound<'a>;
    type SerializeTuple = Compound<'a>;
    type SerializeTupleStruct = Compound<'a>;
    type SerializeTupleVariant = Compound<'a>;
    type SerializeMap = Compound<'a>;
    type SerializeStruct = Compound<'a>;
    type SerializeStructVariant = Compound<'a>;
    fn is_human_readable(&self) -> bool {
        false
    }
    fn serialize_bool(self, v: bool) -> Result<()> {
        self.0.push(if v { TRUE } else { FALSE });
        Ok(())
    }
    integer_ser!(serialize_i8:i8=>serialize_i64,serialize_i16:i16=>serialize_i64,serialize_i32:i32=>serialize_i64,serialize_u8:u8=>serialize_u64,serialize_u16:u16=>serialize_u64,serialize_u32:u32=>serialize_u64);
    fn serialize_i64(self, v: i64) -> Result<()> {
        self.0.push(INT);
        self.count(((v << 1) ^ (v >> 63)) as u64);
        Ok(())
    }
    fn serialize_u64(self, v: u64) -> Result<()> {
        self.0.push(UINT);
        self.count(v);
        Ok(())
    }
    fn serialize_f32(self, v: f32) -> Result<()> {
        self.serialize_f64(v as f64)
    }
    fn serialize_f64(self, v: f64) -> Result<()> {
        self.0.push(FLOAT);
        self.0.extend_from_slice(&v.to_le_bytes());
        Ok(())
    }
    fn serialize_char(self, v: char) -> Result<()> {
        self.serialize_str(v.encode_utf8(&mut [0; 4]))
    }
    fn serialize_str(self, v: &str) -> Result<()> {
        let index = if let Some(&index) = self.1.get(v) {
            index
        } else {
            let text: std::sync::Arc<str> = v.into();
            let index = self.2.len() as u64;
            self.2.push(text.clone());
            self.1.insert(text, index);
            index
        };
        self.0.push(STR);
        self.count(index);
        Ok(())
    }
    fn serialize_bytes(self, v: &[u8]) -> Result<()> {
        self.collection(BYTES, v.len());
        self.0.extend_from_slice(v);
        Ok(())
    }
    fn serialize_none(self) -> Result<()> {
        self.serialize_unit()
    }
    fn serialize_some<T: Serialize + ?Sized>(self, v: &T) -> Result<()> {
        self.0.push(SOME);
        v.serialize(self)
    }
    fn serialize_unit(self) -> Result<()> {
        self.0.push(UNIT);
        Ok(())
    }
    fn serialize_unit_struct(self, _: &'static str) -> Result<()> {
        self.serialize_unit()
    }
    fn serialize_unit_variant(self, _: &'static str, i: u32, _: &'static str) -> Result<()> {
        self.variant(i);
        Ok(())
    }
    fn serialize_newtype_struct<T: Serialize + ?Sized>(self, _: &'static str, v: &T) -> Result<()> {
        v.serialize(self)
    }
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _: &'static str,
        i: u32,
        _: &'static str,
        v: &T,
    ) -> Result<()> {
        self.variant(i);
        v.serialize(self)
    }
    fn serialize_seq(self, n: Option<usize>) -> Result<Compound<'a>> {
        self.collection(SEQ, n.ok_or_else(bad)?);
        Ok(Compound(self))
    }
    fn serialize_tuple(self, _: usize) -> Result<Compound<'a>> {
        Ok(Compound(self))
    }
    fn serialize_tuple_struct(self, _: &'static str, n: usize) -> Result<Compound<'a>> {
        self.serialize_tuple(n)
    }
    fn serialize_tuple_variant(
        self,
        _: &'static str,
        i: u32,
        _: &'static str,
        n: usize,
    ) -> Result<Compound<'a>> {
        self.variant(i);
        self.serialize_tuple(n)
    }
    fn serialize_map(self, n: Option<usize>) -> Result<Compound<'a>> {
        self.collection(MAP, n.ok_or_else(bad)?);
        Ok(Compound(self))
    }
    fn serialize_struct(self, _: &'static str, n: usize) -> Result<Compound<'a>> {
        self.serialize_tuple(n)
    }
    fn serialize_struct_variant(
        self,
        _: &'static str,
        i: u32,
        _: &'static str,
        n: usize,
    ) -> Result<Compound<'a>> {
        self.variant(i);
        self.serialize_tuple(n)
    }
}
macro_rules! compound {
    ($trait:ident,$method:ident) => {
        impl ser::$trait for Compound<'_> {
            type Ok = ();
            type Error = Error;
            fn $method<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<()> {
                v.serialize(&mut *self.0)
            }
            fn end(self) -> Result<()> {
                Ok(())
            }
        }
    };
}
compound!(SerializeSeq, serialize_element);
compound!(SerializeTuple, serialize_element);
compound!(SerializeTupleStruct, serialize_field);
compound!(SerializeTupleVariant, serialize_field);
impl ser::SerializeMap for Compound<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_key<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<()> {
        v.serialize(&mut *self.0)
    }
    fn serialize_value<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<()> {
        v.serialize(&mut *self.0)
    }
    fn end(self) -> Result<()> {
        Ok(())
    }
}
macro_rules! compound_struct {
    ($trait:ident) => {
        impl ser::$trait for Compound<'_> {
            type Ok = ();
            type Error = Error;
            fn serialize_field<T: Serialize + ?Sized>(
                &mut self,
                _: &'static str,
                v: &T,
            ) -> Result<()> {
                v.serialize(&mut *self.0)
            }
            fn end(self) -> Result<()> {
                Ok(())
            }
        }
    };
}
compound_struct!(SerializeStruct);
compound_struct!(SerializeStructVariant);
struct Reader<'de> {
    bytes: &'de [u8],
    depth: usize,
    strings: Vec<&'de str>,
}
impl<'de> Reader<'de> {
    #[inline]
    fn take(&mut self, n: usize) -> Result<&'de [u8]> {
        if n > self.bytes.len() {
            return Err(bad());
        }
        let (v, rest) = self.bytes.split_at(n);
        self.bytes = rest;
        Ok(v)
    }
    #[inline]
    fn tag(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }
    #[inline]
    fn count(&mut self) -> Result<u64> {
        let mut n = 0;
        for shift in (0..70).step_by(7) {
            let b = self.tag()?;
            if shift == 63 && b > 1 {
                return Err(bad());
            }
            n |= ((b & 127) as u64) << shift;
            if b < 128 {
                return Ok(n);
            }
        }
        Err(bad())
    }
    #[inline]
    fn length(&mut self) -> Result<usize> {
        let n = usize::try_from(self.count()?).map_err(|_| bad())?;
        if n > self.bytes.len() {
            return Err(bad());
        }
        Ok(n)
    }
}
struct Access<'a, 'de> {
    r: &'a mut Reader<'de>,
    remaining: usize,
}
impl<'de> SeqAccess<'de> for Access<'_, 'de> {
    type Error = Error;
    fn next_element_seed<T: DeserializeSeed<'de>>(&mut self, seed: T) -> Result<Option<T::Value>> {
        if self.remaining == 0 {
            return Ok(None);
        }
        self.remaining -= 1;
        seed.deserialize(&mut *self.r).map(Some)
    }
    fn size_hint(&self) -> Option<usize> {
        Some(self.remaining.min(1_048_576))
    }
}
impl<'de> MapAccess<'de> for Access<'_, 'de> {
    type Error = Error;
    fn next_key_seed<T: DeserializeSeed<'de>>(&mut self, seed: T) -> Result<Option<T::Value>> {
        self.next_element_seed(seed)
    }
    fn next_value_seed<T: DeserializeSeed<'de>>(&mut self, seed: T) -> Result<T::Value> {
        seed.deserialize(&mut *self.r)
    }
    fn size_hint(&self) -> Option<usize> {
        Some(self.remaining.min(1_048_576))
    }
}
impl<'de> de::Deserializer<'de> for &mut Reader<'de> {
    type Error = Error;
    fn is_human_readable(&self) -> bool {
        false
    }
    fn deserialize_any<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        match self.bytes.first() {
            Some(&SEQ) => return self.collection(v, false),
            Some(&MAP) => return self.collection(v, true),
            _ => {}
        }
        if self.depth >= 256 {
            return Err(bad());
        }
        self.depth += 1;
        let result = match self.tag()? {
            UNIT => v.visit_unit(),
            FALSE => v.visit_bool(false),
            TRUE => v.visit_bool(true),
            UINT => v.visit_u64(self.count()?),
            INT => {
                let n = self.count()?;
                v.visit_i64(((n >> 1) as i64) ^ -((n & 1) as i64))
            }
            FLOAT => v.visit_f64(f64::from_le_bytes(
                self.take(8)?.try_into().map_err(|_| bad())?,
            )),
            STR => {
                let index = usize::try_from(self.count()?).map_err(|_| bad())?;
                v.visit_borrowed_str(self.strings.get(index).copied().ok_or_else(bad)?)
            }
            BYTES => {
                let n = self.length()?;
                v.visit_borrowed_bytes(self.take(n)?)
            }
            _ => Err(bad()),
        };
        self.depth -= 1;
        result
    }
    fn deserialize_seq<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        self.collection(v, false)
    }
    fn deserialize_map<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        self.collection(v, true)
    }
    fn deserialize_tuple<V: Visitor<'de>>(self, n: usize, v: V) -> Result<V::Value> {
        self.fixed(v, n)
    }
    fn deserialize_tuple_struct<V: Visitor<'de>>(
        self,
        _: &'static str,
        n: usize,
        v: V,
    ) -> Result<V::Value> {
        self.fixed(v, n)
    }
    fn deserialize_struct<V: Visitor<'de>>(
        self,
        _: &'static str,
        fields: &'static [&'static str],
        v: V,
    ) -> Result<V::Value> {
        self.fixed(v, fields.len())
    }
    fn deserialize_option<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        if self.depth >= 256 {
            return Err(bad());
        }
        self.depth += 1;
        let result = match self.tag()? {
            UNIT => v.visit_none(),
            SOME => v.visit_some(&mut *self),
            _ => Err(bad()),
        };
        self.depth -= 1;
        result
    }
    fn deserialize_newtype_struct<V: Visitor<'de>>(
        self,
        _: &'static str,
        v: V,
    ) -> Result<V::Value> {
        v.visit_newtype_struct(self)
    }
    fn deserialize_enum<V: Visitor<'de>>(
        self,
        _: &'static str,
        _: &'static [&'static str],
        v: V,
    ) -> Result<V::Value> {
        if self.tag()? != ENUM || self.depth >= 256 {
            return Err(bad());
        }
        self.depth += 1;
        let i = u32::try_from(self.count()?).map_err(|_| bad())?;
        let result = v.visit_enum(Variant { r: self, index: i });
        self.depth -= 1;
        result
    }
    fn deserialize_u64<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        if self.bytes.first() != Some(&UINT) {
            return self.deserialize_any(v);
        }
        self.bytes = &self.bytes[1..];
        v.visit_u64(self.count()?)
    }
    fn deserialize_i64<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        if self.bytes.first() != Some(&INT) {
            return self.deserialize_any(v);
        }
        self.bytes = &self.bytes[1..];
        let n = self.count()?;
        v.visit_i64(((n >> 1) as i64) ^ -((n & 1) as i64))
    }
    fn deserialize_bool<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        match self.bytes.first() {
            Some(&TRUE) | Some(&FALSE) => {
                let b = self.bytes[0] == TRUE;
                self.bytes = &self.bytes[1..];
                v.visit_bool(b)
            }
            _ => self.deserialize_any(v),
        }
    }
    fn deserialize_str<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        if self.bytes.first() != Some(&STR) {
            return self.deserialize_any(v);
        }
        self.bytes = &self.bytes[1..];
        let i = usize::try_from(self.count()?).map_err(|_| bad())?;
        v.visit_borrowed_str(self.strings.get(i).copied().ok_or_else(bad)?)
    }
    fn deserialize_string<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        self.deserialize_str(v)
    }
    fn deserialize_u8<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        self.deserialize_u64(v)
    }
    fn deserialize_u16<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        self.deserialize_u64(v)
    }
    fn deserialize_u32<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        self.deserialize_u64(v)
    }
    fn deserialize_i8<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        self.deserialize_i64(v)
    }
    fn deserialize_i16<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        self.deserialize_i64(v)
    }
    fn deserialize_i32<V: Visitor<'de>>(self, v: V) -> Result<V::Value> {
        self.deserialize_i64(v)
    }
    serde::forward_to_deserialize_any! { f32 f64 char bytes byte_buf unit unit_struct identifier ignored_any }
}
impl<'de> Reader<'de> {
    fn fixed<V: Visitor<'de>>(&mut self, v: V, n: usize) -> Result<V::Value> {
        if self.depth >= 256 {
            return Err(bad());
        }
        self.depth += 1;
        let mut access = Access {
            r: self,
            remaining: n,
        };
        let result = v.visit_seq(&mut access);
        let remaining = access.remaining;
        self.depth -= 1;
        if remaining != 0 {
            return Err(bad());
        }
        result
    }
    fn collection<V: Visitor<'de>>(&mut self, v: V, map: bool) -> Result<V::Value> {
        if self.depth >= 256 || self.tag()? != if map { MAP } else { SEQ } {
            return Err(bad());
        }
        self.depth += 1;
        let n = usize::try_from(self.count()?).map_err(|_| bad())?;
        // Fixed empty records occupy no payload bytes, so element counts
        // have a separate bound instead of assuming one byte per element.
        if n > 1_048_576 {
            return Err(bad());
        }
        let mut a = Access {
            r: self,
            remaining: n,
        };
        let result = if map {
            v.visit_map(&mut a)
        } else {
            v.visit_seq(&mut a)
        };
        let left = a.remaining;
        self.depth -= 1;
        if left != 0 {
            return Err(bad());
        }
        result
    }
}
struct Variant<'a, 'de> {
    r: &'a mut Reader<'de>,
    index: u32,
}
impl<'a, 'de> EnumAccess<'de> for Variant<'a, 'de> {
    type Error = Error;
    type Variant = Self;
    fn variant_seed<V: DeserializeSeed<'de>>(self, seed: V) -> Result<(V::Value, Self)> {
        Ok((seed.deserialize(self.index.into_deserializer())?, self))
    }
}
impl<'de> VariantAccess<'de> for Variant<'_, 'de> {
    type Error = Error;
    fn unit_variant(self) -> Result<()> {
        Ok(())
    }
    fn newtype_variant_seed<T: DeserializeSeed<'de>>(self, seed: T) -> Result<T::Value> {
        seed.deserialize(&mut *self.r)
    }
    fn tuple_variant<V: Visitor<'de>>(self, n: usize, v: V) -> Result<V::Value> {
        de::Deserializer::deserialize_tuple(&mut *self.r, n, v)
    }
    fn struct_variant<V: Visitor<'de>>(
        self,
        fields: &'static [&'static str],
        v: V,
    ) -> Result<V::Value> {
        de::Deserializer::deserialize_struct(&mut *self.r, "", fields, v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    enum Choice {
        Empty,
        Value(Option<Option<i64>>),
        Pair(String, u64),
        Fields { value: f64 },
    }
    #[test]
    fn binary_cache_preserves_numbers_variants_options_and_tuple_keys() {
        let choices = vec![
            Choice::Empty,
            Choice::Value(None),
            Choice::Value(Some(None)),
            Choice::Value(Some(Some(i64::MIN))),
            Choice::Pair("é".into(), u64::MAX),
            Choice::Fields { value: -0.0 },
        ];
        let bytes = encode(&choices).unwrap();
        assert_eq!(decode::<Vec<Choice>>(&bytes).unwrap(), choices);
        let value = serde_json::json!({"signed":i64::MIN,"unsigned":u64::MAX,"float":1e-28,"empty":null,"array":[true,false,{},[]]});
        assert_eq!(
            decode::<serde_json::Value>(&encode(&value).unwrap()).unwrap(),
            value
        );
        let map = std::collections::HashMap::from([((42usize, "name".to_string()), Some(8usize))]);
        assert_eq!(
            decode::<std::collections::HashMap<(usize, String), Option<usize>>>(
                &encode(&map).unwrap()
            )
            .unwrap(),
            map
        );
        for cut in 0..bytes.len() {
            assert!(decode::<Vec<Choice>>(&bytes[..cut]).is_err());
        }
        let mut trailing = bytes;
        trailing.push(UNIT);
        assert!(decode::<Vec<Choice>>(&trailing).is_err());
        assert!(
            decode::<Vec<Choice>>(&[SEQ, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255])
                .is_err()
        );
    }
}

#[cfg(test)]
mod string_table_tests {
    use super::*;
    #[test]
    fn repeated_strings_are_interned_and_invalid_tables_are_rejected() {
        let values = vec!["a long repeated property and qualified name".to_owned(); 100];
        let encoded = encode(&values).unwrap();
        assert!(encoded.len() < 300);
        assert_eq!(decode::<Vec<String>>(&encoded).unwrap(), values);
        // No strings but a string reference, truncated string, invalid UTF-8,
        // and an out-of-bounds reference to a one-entry table.
        for bytes in [
            vec![0, STR, 0],
            vec![1, 2, b'a'],
            vec![1, 1, 255, UNIT],
            vec![1, 1, b'a', STR, 1],
        ] {
            assert!(decode::<String>(&bytes).is_err());
        }
    }
}

// Only active during this decoder's call. Table slices remain alive throughout
// it, so a borrowed string's address identifies its table entry. No raw pointer
// is dereferenced. Nested decodes get independent tables; the guard restores
// the previous context on both normal returns and unwinding.
type StringPool = std::collections::HashMap<(usize, usize), std::sync::Arc<str>>;
thread_local! {
    static SHARED_STRINGS: std::cell::RefCell<Option<StringPool>> = const { std::cell::RefCell::new(None) };
}
struct SharedStrings(Option<StringPool>);
impl SharedStrings {
    fn enter() -> Self {
        Self(SHARED_STRINGS.with(|v| v.replace(Some(Default::default()))))
    }
}
impl Drop for SharedStrings {
    fn drop(&mut self) {
        SHARED_STRINGS.with(|v| {
            v.replace(self.0.take());
        });
    }
}
pub(crate) fn shared_string<'de, D: serde::Deserializer<'de>>(
    d: D,
) -> std::result::Result<std::sync::Arc<str>, D::Error> {
    struct Text;
    impl serde::de::Visitor<'_> for Text {
        type Value = std::sync::Arc<str>;
        fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.write_str("a string")
        }
        fn visit_str<E: serde::de::Error>(self, s: &str) -> std::result::Result<Self::Value, E> {
            Ok(s.into())
        }
        fn visit_borrowed_str<E: serde::de::Error>(
            self,
            s: &str,
        ) -> std::result::Result<Self::Value, E> {
            Ok(SHARED_STRINGS.with(|pool| {
                let mut pool = pool.borrow_mut();
                let Some(pool) = pool.as_mut() else {
                    return s.into();
                };
                let value = pool
                    .entry((s.as_ptr() as usize, s.len()))
                    .or_insert_with(|| s.into());
                // Also safe for another serde source used within a decode.
                if value.as_ref() != s {
                    *value = s.into();
                }
                value.clone()
            }))
        }
    }
    d.deserialize_str(Text)
}

#[cfg(test)]
mod shared_text_tests {
    use super::*;
    use std::sync::Arc;
    #[derive(Serialize, Deserialize)]
    struct Text(#[serde(deserialize_with = "shared_string")] Arc<str>);
    #[test]
    fn repeated_text_is_shared_and_decode_contexts_do_not_escape() {
        let source = vec![Text("repeated name".into()), Text("repeated name".into())];
        let bytes = encode(&source).unwrap();
        let first: Vec<Text> = decode(&bytes).unwrap();
        assert!(Arc::ptr_eq(&first[0].0, &first[1].0));
        assert!(SHARED_STRINGS.with(|s| s.borrow().is_none()));
        let next: Vec<Text> = decode(&bytes).unwrap();
        assert!(!Arc::ptr_eq(&first[0].0, &next[0].0));
        assert!(decode::<Vec<Text>>(&bytes[..bytes.len() - 1]).is_err());
        assert!(SHARED_STRINGS.with(|s| s.borrow().is_none()));
        let outer = SharedStrings::enter();
        {
            let _inner = SharedStrings::enter();
        }
        assert!(SHARED_STRINGS.with(|s| s.borrow().is_some()));
        drop(outer);
        assert!(SHARED_STRINGS.with(|s| s.borrow().is_none()));
    }
}

#[cfg(test)]
mod record_tests {
    use super::*;
    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    struct Empty {}
    #[test]
    fn fixed_records_preserve_zero_width_values_and_bound_counts() {
        let values = vec![Empty {}, Empty {}, Empty {}];
        assert_eq!(
            decode::<Vec<Empty>>(&encode(&values).unwrap()).unwrap(),
            values
        );
        let mut w = Writer::default();
        w.count(0);
        w.collection(SEQ, 1_048_577);
        assert!(decode::<Vec<Empty>>(&w.0).is_err());
        let tuple = (17u32, "text", Some(false));
        assert_eq!(
            decode::<(u32, String, Option<bool>)>(&encode(&tuple).unwrap()).unwrap(),
            (17, "text".into(), Some(false))
        );
    }
}
