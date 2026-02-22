// Site search with Lunr.js
(function() {
  let searchIndex = null;
  let searchData = null;

  // Load search data and build index
  async function initSearch() {
    try {
      const response = await fetch('/logic-realism-theory/search.json');
      searchData = await response.json();

      searchIndex = lunr(function() {
        this.ref('url');
        this.field('title', { boost: 10 });
        this.field('content');

        searchData.forEach((doc, idx) => {
          this.add({
            url: doc.url,
            title: doc.title,
            content: doc.content
          });
        });
      });
    } catch (e) {
      console.error('Failed to load search index:', e);
    }
  }

  // Perform search and return results
  function search(query) {
    if (!searchIndex || !query) return [];

    try {
      const results = searchIndex.search(query + '*');
      return results.slice(0, 8).map(result => {
        const doc = searchData.find(d => d.url === result.ref);
        return doc;
      }).filter(Boolean);
    } catch (e) {
      // Fallback to simple search if Lunr query fails
      const q = query.toLowerCase();
      return searchData.filter(doc =>
        doc.title.toLowerCase().includes(q) ||
        doc.content.toLowerCase().includes(q)
      ).slice(0, 8);
    }
  }

  // Render search results
  function renderResults(results, container) {
    if (results.length === 0) {
      container.innerHTML = '<div class="search-no-results">No results found</div>';
      return;
    }

    container.innerHTML = results.map(doc => `
      <a href="${doc.url}" class="search-result">
        <div class="search-result-title">${doc.title}</div>
        <div class="search-result-excerpt">${doc.excerpt}</div>
      </a>
    `).join('');
  }

  // Initialize when DOM is ready
  document.addEventListener('DOMContentLoaded', function() {
    const searchInput = document.getElementById('site-search');
    const searchResults = document.getElementById('search-results');

    if (!searchInput || !searchResults) return;

    initSearch();

    let debounceTimer;
    searchInput.addEventListener('input', function() {
      clearTimeout(debounceTimer);
      const query = this.value.trim();

      if (query.length < 2) {
        searchResults.classList.remove('active');
        return;
      }

      debounceTimer = setTimeout(() => {
        const results = search(query);
        renderResults(results, searchResults);
        searchResults.classList.add('active');
      }, 150);
    });

    // Close results when clicking outside
    document.addEventListener('click', function(e) {
      if (!e.target.closest('.search-wrapper')) {
        searchResults.classList.remove('active');
      }
    });

    // Close on Escape
    searchInput.addEventListener('keydown', function(e) {
      if (e.key === 'Escape') {
        searchResults.classList.remove('active');
        this.blur();
      }
    });
  });
})();
