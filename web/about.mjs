const articles=[...document.querySelectorAll('article[lang]')];
function update(){
  const requested=location.hash.slice(1);
  const selected=articles.find(a=>a.id===requested)||articles[0];
  for(const a of articles)a.hidden=a!==selected;
  document.documentElement.lang=selected.lang;
  for(const a of document.querySelectorAll('.about-nav nav a')){
    if(a.hash==='#'+selected.id)a.setAttribute('aria-current','page');
    else a.removeAttribute('aria-current');
  }
}
window.addEventListener('hashchange',update);update();
