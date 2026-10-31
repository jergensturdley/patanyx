//! Page-opened windows held open while the tab that receives them is built.
//!
//! On Windows a page's `window.open()` or `target="_blank"` form is answered by
//! handing the engine a webview of our own (`put_NewWindow`), so the new tab
//! gets the engine's navigation with its method, body, referrer and opener.
//! A plain new tab loading the same address with GET loses the body, which is
//! why a booking hand-off (Google Flights to the airline) or a payment popup
//! failed. The engine waits on a deferral while that tab is built; this table
//! holds the deferred requests until then.
//!
//! The table only stores. What an entry does when it is dropped is the
//! entry's business, and on Windows that is to answer the engine with no
//! window, so every path that loses an entry -- refused, over the cap, tab
//! failed, tab closed first -- still answers the page. Nothing here is ever
//! left deferred.
//!
//! Entries are removed BEFORE they are dropped, so dropping one (a COM call
//! on Windows) never runs while the table is borrowed.

#![cfg_attr(not(windows), allow(dead_code))]

use std::collections::BTreeMap;

/// More outstanding requests than this and new ones are answered at once with
/// no window. Each one costs a tab build, and a page asking for this many
/// tabs before the first is built is not one a person is using.
pub const MAX_PENDING: usize = 8;

pub struct PendingTable<T> {
    next: u64,
    entries: BTreeMap<u64, T>,
}

impl<T> Default for PendingTable<T> {
    fn default() -> Self {
        Self {
            next: 1,
            entries: BTreeMap::new(),
        }
    }
}

impl<T> PendingTable<T> {
    /// Holds `entry` and returns its token, or hands it back when the table
    /// is full so the caller drops it outside any borrow.
    pub fn insert(&mut self, entry: T) -> Result<u64, T> {
        if self.entries.len() >= MAX_PENDING {
            return Err(entry);
        }
        let token = self.next;
        self.next += 1;
        self.entries.insert(token, entry);
        Ok(token)
    }

    /// Removes and returns the entry for `token`. A token is good once.
    pub fn take(&mut self, token: u64) -> Option<T> {
        self.entries.remove(&token)
    }

    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.entries.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::rc::Rc;

    /// Counts its own drops, the way a Windows entry answers the engine.
    struct Answers(Rc<Cell<u32>>);

    impl Drop for Answers {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    #[test]
    fn an_entry_is_answered_once_whichever_way_it_leaves() {
        let answered = Rc::new(Cell::new(0));
        let mut table = PendingTable::default();
        let token = table.insert(Answers(answered.clone())).ok().unwrap();
        assert_eq!(answered.get(), 0, "held, not answered");
        let entry = table.take(token).expect("the token names it");
        assert!(table.take(token).is_none(), "a token is good once");
        drop(entry);
        assert_eq!(answered.get(), 1);
    }

    #[test]
    fn past_the_cap_a_request_is_handed_back_to_be_answered() {
        let answered = Rc::new(Cell::new(0));
        let mut table = PendingTable::default();
        for _ in 0..MAX_PENDING {
            assert!(table.insert(Answers(answered.clone())).is_ok());
        }
        let refused = table.insert(Answers(answered.clone()));
        assert!(refused.is_err());
        drop(refused);
        assert_eq!(answered.get(), 1, "the refused one is answered at once");
        assert_eq!(table.len(), MAX_PENDING);
        drop(table);
        assert_eq!(answered.get(), 1 + MAX_PENDING as u32, "dropping the table answers the rest");
    }

    #[test]
    fn tokens_are_never_reused() {
        let mut table = PendingTable::default();
        let first = table.insert(()).ok().unwrap();
        table.take(first);
        let second = table.insert(()).ok().unwrap();
        assert_ne!(first, second, "a stale token cannot reach a newer request");
    }
}
