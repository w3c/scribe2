const recordingUrl = document.getElementById("recording")?.querySelector("a")?.href;

const embed = document.getElementById("recording")?.querySelector("iframe");
let playing = false;

const sendVideoCommand = (command, args) => {
  let msg;
  if (embed.src.match(/^https:\/\/(www\.)?youtube\.com\//)) {
    const commands = {'play': 'playVideo', 'pause': 'pauseVideo', 'seek': 'seekTo'};
    msg = JSON.stringify({
      event: 'command',
      func: commands[command],
      args
    });
  } else {
    msg = [command, ...args];
  }
  embed.contentWindow.postMessage(msg, '*');
};
embed.parentNode.parentNode.style.height = "calc(1em + " + embed.height + "px)";
const showVideoIfNeeded = () => {
  const windowScrollTop = window.pageYOffset;
  const {top} = embed.getBoundingClientRect();
  const videoBottom = parseInt(embed.height, 10) + top;
  if (windowScrollTop > videoBottom && playing) {
    embed.parentNode.classList.add('stuck');
  } else {
    embed.parentNode.classList.remove('stuck');
  }
};

const videoPlayHandler = (e) => {
  if (!embed) return;
  const el = e.target;
  const offset = parseInt(el.dataset.offset, 10);
  if (offset && !isNaN(offset) && !el.dataset.lastHit) {
    sendVideoCommand('seek', [offset]);
  }
  sendVideoCommand('play');
  playing = true;
  showVideoIfNeeded();
  document.querySelectorAll("button.playBtn").forEach(el => delete el.dataset.lastHit);
  el.dataset.lastHit = true;
};

const videoPauseHandler = (e) => {
  if (!embed) return;
  sendVideoCommand('pause');
  playing = false;
};

if (recordingUrl) {
  document.querySelectorAll("a.recording[href]").forEach(el => {
    // Add play/pause button
    const playBtn = document.createElement("button");
    playBtn.className = "playBtn";
    playBtn.dataset.offset = new URL(el.href).hash.split("=")[1];
    el.insertAdjacentElement("afterend", playBtn);
    playBtn.addEventListener("click", videoPlayHandler);
    playBtn.title = "Play embedded recording from that point of the meeting";
    playBtn.textContent = "▶";

    const pauseBtn = document.createElement("button");
    playBtn.insertAdjacentElement("afterend", pauseBtn);
    pauseBtn.addEventListener("click", videoPauseHandler);
    pauseBtn.title = "Pause embedded recording";
    pauseBtn.textContent = "⏸";
  });

  window.addEventListener("scroll", showVideoIfNeeded, {passive: true});
}

